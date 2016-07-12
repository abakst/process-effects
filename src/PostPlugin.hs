module PostPlugin
    ( lhplug
    ) where

import Debug.Trace
import Data.Maybe
import Data.List as L
import Data.Map.Strict as M
import Data.HashMap.Strict as H
import Control.Monad.Reader
import Control.Monad.State
import Text.PrettyPrint.HughesPJ
import Text.Printf
import System.IO.Unsafe

import GHC
import Var
import Type
import DataCon
import Name
import CoreSyn
import CoreUtils
import Outputable
import PrelNames
import HscTypes hiding (lookupType)
import Annotations
import UniqFM
import Serialized
import IdInfo
import DynFlags

import EffectTypes  
import PrettyPrint
import Parse

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Plugin as P
import Language.Haskell.Liquid.GHC.Misc
-- import Language.Haskell.Liquid.Types.PrettyPrint as PP
import Language.Haskell.Liquid.UX.Tidy

import Language.Fixpoint.Types hiding (PPrint(..), SrcSpan(..), ECon) 
import qualified Language.Fixpoint.Types as Fp

debug s x = trace (s ++ ": " ++ show x) x  

lhplug :: Plugin
lhplug = PostPlugin { P.name   = "gloob(ic) v 2"
                    , P.plugin = DoPostStep doEffects
                    }

data EffState = EffState {
    ctr :: Int
  , annots :: H.HashMap SrcSpan [SpecType]
  , annenv :: AnnEnv
  , tyconEmb :: TCEmb TyCon
  , tsubst :: [(Symbol, EffTy)]
  , esubst :: [(Symbol, Effect)]
  }
type EffectM a = StateT EffState IO a

type EffEnv = M.Map Name EffTy
freshInt = do n <- gets ctr
              modify $ \s -> s { ctr = n + 1}
              return n
freshEffVar = do n <- freshInt
                 return (symbol ("η" ++ show n))
freshTermVar = do n <- freshInt
                  return (symbol ("x" ++ show n))
freshChanVar = do n <- freshInt
                  return (symbol ("p" ++ show n))
freshEffTyVar = do n <- freshInt
                   return (ETyVar (symbol ("E" ++ show n)))

freshFnEff :: EffTy -> EffectM EffTy
freshFnEff t@(EForAll s e)
  = do v <- freshEffTyVar
       freshFnEff (sub [(s, v)] e)
freshFnEff t@(ETermAbs s e)
  = do v <- freshEffVar
       freshFnEff (sub [(s, EffVar (Eff v))] e)
freshFnEff t@(EPi s e1 e2)
  = do s'  <- freshTermVar
       e2' <- freshChans e2
       return $ EPi s' e1 (sub [(s, s')] e2')
freshFnEff t
  = return t

freshChans (EffTerm e)
  = EffTerm <$> go e
  where
    go (Nu s e) = do v <- freshChanVar
                     let e' = sub [(s,v)] e
                     Nu v <$> go e'
    go (Par e1 e2) = Par <$> go e1 <*> go e2
    go (Pend e xt) = Pend <$> go e <*> pure xt
    go (AppEff e1 e2)
      = AppEff <$> go e1 <*> go e2
    go (AbsEff b e) = AbsEff b <$> go e
    go (Bind e1 e2) = Bind <$> go e1 <*> go e2
    go e = return e
freshChans e = return e

printEffTerm = render . pretty

printEff :: EffTy -> String
printEff EffNone
  = "Λ"
printEff (ETyVar s)
  = symbolString s
printEff (EForAll s t)
  = printf "∀%s. %s" (symbolString s) (printEff t)
printEff (EPi s e1 e2)
  = printf "(%s:%s -> %s)" (symbolString s) (printEff e1) (printEff e2)
printEff (ETyApp e1 e2)
  = printf "(%s %s)" (printEff e1) (printEff e2)
printEff (ETermAbs s e)
  = printf "∀%s. (%s)" (symbolString s) (printEff e)
printEff (EffTerm t)
  = printf "{ %s }" (printEffTerm t)

kont = Eff (symbol "$K")
me   = Src (symbol "me")
noEff = EffNone --EffLit "0"
callCC = absEff kont
withPid = absEff me
absEff x e = AbsEff x e          

effBindF = callCC . withPid             

bindEffectTy = ETermAbs e0Sym
             $ ETermAbs e1Sym
             $ EPi actSym (EffTerm (EffVar (Eff e0Sym)))
             $ EPi fSym
                 (EPi xSym noEff
                        (EffTerm (EffVar (Eff e1Sym))))
                 (EffTerm (absEff (Src actSym)
                          (absEff (Src fSym)
                          (effBindF
                           (AppEff (AppEff (EffVar (Eff e0Sym))
                                    (AbsEff (Src (symbol "_0"))
                                      (AppEff (AppEff (AppEff (EffVar (Eff e1Sym))
                                                              (EffVar (Src (symbol "_0"))))
                                                      (EffVar kont))
                                              (EffVar me))))
                            (EffVar me))))))
  where
    fSym = symbol "f"
    actSym = symbol "act"
    e0Sym = symbol "e0"
    e1Sym = symbol "e1"
    xSym = symbol "x"

thenEffectTy = ETermAbs e0Sym
             $ ETermAbs e1Sym
             $ EPi fSym (EffTerm (EffVar (Eff e0Sym)))
             $ EPi gSym (EffTerm (EffVar (Eff e1Sym)))
             $ EffTerm (absEff (Src fSym)
                                 (effBindF (AppEff (AppEff (EffVar (Eff e0Sym))
                                              (AbsEff (Src (symbol "_")) (EffVar (Eff e1Sym))))
                                            (EffVar me))))
  where
    fSym = symbol "f"
    gSym = symbol "g"
    e0Sym = symbol "e0"
    e1Sym = symbol "e1"

withCC = ETermAbs (symbol "K")           

doEffects :: AnnInfo SpecType -> ReaderT PluginEnv IO ()
doEffects (AI m)
  = do core <- reader P.cbs
       hsenv <- env <$> reader ghcInfo
       emb <- reader embed
       liftIO $ do
         setUnsafeGlobalDynFlags (extractDynFlags hsenv)
         annenv <- prepareAnnotations hsenv Nothing
         evalStateT (synthEffects M.empty core) EffState { ctr = 0
                                                         , annots = m'
                                                         , annenv = annenv
                                                         , tyconEmb = emb
                                                         , esubst = []
                                                         , tsubst = []
                                                         }
  where
    m' = (snd <$>) <$> m

lookupAnn :: Id -> EffectM [String]
lookupAnn v
  = do e <- gets annenv
       -- let anns = deserializeAnns deserializeWithData e
       let tgt = NamedTarget (getName v)
       -- liftIO $ do putStrLn "allAnns"
       --             forM (ufmToList anns) put
       return $ findAnns deserializeWithData e tgt
  where
    put :: Show a => (a, [String]) -> IO ()
    put x = putStrLn (show x)

synthEffects :: EffEnv -> [CoreBind] -> EffectM ()
synthEffects g []
  = return ()
synthEffects g (cb:cbs)
  = do g' <- synth1Effect g cb
       synthEffects g' cbs

synth1Effect :: EffEnv -> CoreBind -> EffectM EffEnv 
synth1Effect g (NonRec b e)
  = do et  <-  dbgTy "got" =<< applySubstM =<< synthEff g e
       g'  <-  mapM applySubstM g
       let egen = generalizeEff g' et
       liftIO $ putStrLn (printf "%s : %s" (getOccString b) (printEff $ betaReduceTy egen))
       return (M.insert (getName b) (generalizeEff g' egen) g')

synth1Effect g (Rec [(b,e)])              
  = do tv <- freshEffTyVar
       let g' = M.insert (getName b) tv g
       et <- applySubstM =<< synthEff g' e
       betaReduceTy <$> applySubstM et
       applySubstM tv
       error "adsfl"

lookupEff :: EffEnv -> CoreExpr -> EffectM EffTy
lookupEff g e@(Var x)
  | isRecordSel x
    = return $ EPi (symbol "_") noEff noEff
  where
    isRecordSel x = case idDetails x of
                      RecSelId {} -> True
                      _           -> False
lookupEff g e@(Var x)
  = do t <- case M.lookup (getName x) g of
              Nothing -> do
                defaultEff (CoreUtils.exprType e)
              Just e  -> return e
       return t

bkFun :: Type -> Maybe ([TyVar], [Type], Type)
bkFun t
  = if Type.isFunTy tfun then Just (tvs, targs', tout) else Nothing
  where
    (tvs, tfun)   = splitForAllTys t
    (targs, tout) = splitFunTys tfun
    targs'        = [ t | t <- targs, not (isDictLikeTy t) ]

walkTyVars f t
  | isTyVarTy t
    = return $ f (fromJust (getTyVar_maybe t))
  | otherwise 
    = case bkFun t of
        Just (tvs, ts, tout) -> do
          e:ets <- mapM (walkTyVars f) (tout : reverse ts)
          foldM go e ets
        Nothing ->
          defaultEff t
  where
    go :: EffTy -> EffTy -> EffectM EffTy
    go t t' = do x <- freshTermVar
                 return $ EPi x t' (abstractArg x t)
            

defaultEff :: Type -> EffectM EffTy
defaultEff t
  | isJust (bkFun t)
  = do is <- mapM (const freshInt) tvs
       let evs    = zip tvs (sym <$> is)
           sym    = symbol . ("E" ++) . show
       e:ets <- mapM (walkTyVars (go evs)) $ (tout : reverse targs)
       funTy <- foldM goPi e ets
       return funTy
  where
    Just (tvs, targs, tout) = bkFun t
    go evs tv = maybe noEff ETyVar $ L.lookup tv evs
    goPi t t' = do x <- freshTermVar
                   return $ EPi x t' (abstractArg x t)
-- defaultEff t
--   | Type.isFunTy t
--   = case splitFunTy_maybe t of
--       Just (tin, tout) -> do
--         liftIO $ putStrLn "asdf!!!!!!!!"
--         return noEff
defaultEff t
  = go =<< isEffectType t
  where
    go True = EffTerm <$> EffVar <$> (Eff <$> freshEffVar)
    go _    = return noEff
       

isEffectType :: Type -> EffectM Bool
isEffectType t
  = do e <- gets annenv
       case tyConAppTyCon_maybe t of
         Just tc -> do
           let tgt = NamedTarget (getName tc)
               as  = findAnns deserializeWithData e tgt :: [String]
           -- liftIO (putStrLn ("as " ++ show as))
           return $ "effects" `elem` as
         _ -> return False

synthEff :: EffEnv -> CoreExpr -> EffectM(EffTy)
synthEff g e@(Var x)
  = do as <- lookupAnn x
       eff <- consult as
       freshFnEff eff {- >>= dbgTy "synthEff: Var" -}
       -- liftIO $ putStrLn (show as)
  where
    consult [t] = case parseEffTy t of
                    Right et -> return et
    consult _   = lookupEff g e
synthEff g (Tick _ e)
  = synthEff g e
synthEff g (App e@(Var f) (Type x))
  = isEffectType x >>= lookupFunType >>= freshFnEff
  where
    lookupFunType isEffect
      | isEffect &&
        getName f == bindMName
      = return $ bindEffectTy
      | isEffect &&
        getName f == thenMName
      = return $ thenEffectTy
      | otherwise
      = synthEff g e
synthEff g (App e (Type t))
  = synthEff g e
synthEff g (App e m)
  | not (isTypeArg m) && skip (CoreUtils.exprType m)
  = synthEff g e
  where
    skip t
      | isDictTy t     = True
      | isDictLikeTy t = case splitTyConApp_maybe t of
                           Just (tc, tys) -> not (L.null tys)
                           _ -> True
      | otherwise      = False
synthEff g (Lit l)
  = return $ noEff 
synthEff g (Let b e)
  = do g' <- synth1Effect g b
       synthEff g' e
synthEff g (Lam b e)
  | isTyVar b
  = synthEff g e
  | otherwise
  = do arge  <- defaultEff (varType b)
       te    <- synthEff (M.insert (getName b) arge g) e
       arge' <- applySubstM arge
       return (EPi (symbol b) arge' (abstractArg (symbol b) (betaReduceTy te)))
synthEff g (App eFun eArg)
  = do funEff                     <- dbgTy "funEff" =<<
                                     applySubstM =<<
                                     synthEff g eFun
       argEff                     <- dbgTy "argEff" =<< applySubstM =<<
                                     synthEff g eArg
       v                          <- freshTermVar
       let x = maybe v id $ maybeExtractVar eArg
       e                          <- freshEffTyVar
       EPi s tIn tOut             <- applySubstM =<< unifyTysM funEff (EPi v argEff e)
       reft                       <- lookupSpecType eArg
       liftIO $ putStrLn (printf "applyArg %s" (symbolString x))
       liftIO $ putStrLn (printf "reft %s" (Fp.showpp (rTypeReft reft)))
       applyArg x reft <$> applySubstM tOut
       -- betaReduceTy <$> maybeSubArg s reft <$> applySubstM tOut
  where
    -- maybeSubArg :: Symbol -> SpecType -> EffTy -> EffTy
    -- maybeSubArg s t e
    --   = maybe e (\v -> applyArg (s, Info (v,t)) e) $ maybeExtractVar eArg

synthEff g (Case e x t alts)
  = do es <- mapM (altEffect g) alts
       -- assume EffTerms...
       betaReduceTy <$> joinEffects (symbol ex) es
  where
    app e = AppEff (AppEff e (EffVar kont)) (EffVar me)
    ex = maybe err id $ maybeExtractVar e
    err = error "Not a var (case)"

generalizeEff g
  = gen freeEffTyVars EForAll . gen freeEffTermVars ETermAbs
  where
    gen f c t
      = L.foldr go t free 
      where
        go s t = c s t
        free = fvs L.\\ gvs
        fvs = f t
        gvs = nub (concatMap f $ M.elems g)
    -- generalizeTerm g t
    --   = L.foldr go t free 
    --   where
    --     go s t = ETermAbs s t
    --     free =fvs L.\\ gvs
    --     fvs = freeEffTermVars t
    --     gvs = nub (concatMap freeEffTermVars $ M.elems g)
    -- generalizeTy g t
    

altEffect :: EffEnv -> CoreAlt -> EffectM (Symbol, [Symbol], EffTy)
altEffect g (DataAlt dc, bs, e)
  = do t <- synthEff g e
       return (symbol (dataConName dc), symbol <$> bs, t)
altEffect g (LitAlt _, _, e)
  = return $ (undefined, [], noEff)
altEffect g (DEFAULT, _, _)
  = return $ (undefined, [], noEff)

maybeExtractVar (Var v)     = Just (symbol v)
maybeExtractVar (Tick tt e) = maybeExtractVar e
maybeExtractVar _           = Nothing

applySubstM :: EffTy -> EffectM EffTy                              
applySubstM t
  = do tsu <- gets tsubst
       esu <- gets esubst
       return (sub esu (sub tsu t))

unifyTysM :: EffTy -> EffTy -> EffectM EffTy
unifyTysM t1 t2
  = do tsu <- gets tsubst
       esu <- gets esubst
       (tsu, esu, t) <- unifyTys tsu esu (ap tsu esu t1) (ap tsu esu t2)
       modify $ \s -> s { tsubst = tsu, esubst = esu }
       return t
  where
    ap tsu esu = sub esu . sub tsu

unifyTys tsu esu t1 t2                 
  = do liftIO (putStrLn (printf "UNIFY:\n%s\n%s\n\n\tsubt:(%s)\n\tsube:(%s)" (printEff t1) (printEff t2) (printSubst printEff tsu) (printSubst printEffTerm esu)))
       unifyTermTys tsu esu t1 t2 

unifyTermTys tSub eSub EffNone EffNone
  = return (tSub, eSub, EffNone)
unifyTermTys tSub eSub (ETyVar t) t'
  | t `notElem` dom tSub
  = return (tSub', eSub, t')
  where
    tSub' = tSub `catSubst` [(t, t')]
unifyTermTys tSub eSub t' (ETyVar t)
  | t `notElem` dom tSub
  = return (tSub', eSub, t')
  where
    tSub' = tSub `catSubst` [(t, t')]
unifyTermTys tSub eSub (EffTerm t1) (EffTerm t2)
  = do let (eSub', t) = unifyTerms eSub t1 t2
       return (tSub, eSub', EffTerm t)
unifyTermTys tSub eSub f@(EPi s t1 t2) (EPi s' t1' t2')
  = do v                     <- freshTermVar
       (tSub1, eSub1, tyIn)  <- unifyTys tSub eSub (sub [(s,v)] t1) (sub [(s',v)] t1')
       let ap = sub eSub1 . sub tSub1 
       (tSub2, eSub2, tyOut) <- unifyTys tSub1 eSub1 (ap $ sub [(s,v)] t2) (ap $ sub [(s',v)] t2')
       return (sub eSub2 (sub eSub1 tSub2), eSub2, EPi v tyIn tyOut)
unifyTermTys tSub eSub (ETermAbs s t) (ETermAbs s' t')
  = do e         <- freshEffVar
       let inst  = [(s, EffVar (Eff e))]
       (tSub, eSub, t'') <- unifyTys tSub eSub (sub inst t) (sub inst t')
       return (tSub, eSub, ETermAbs e t'')
unifyTermTys tSub eSub t@(ETermAbs _ _) t'
  = do e <- freshEffVar
       unifyTys tSub eSub t (ETermAbs e t')
unifyTermTys tSub eSub t t'@(ETermAbs _ _)
  = do e <- freshEffVar
       unifyTys tSub eSub (ETermAbs e t) t'
unifyTermTys tsub esub t1 t2
  = error oops  -- (printEff t1) (printEff t2))
  where
    oops = printf "%s unify %s\nsubt:(%s)\nsube:(%s)" (printEff t1) (printEff t2) (printSubst printEff tsub) (printSubst printEffTerm esub)

unifyTerms su (EffVar (Eff t)) e
  | t `notElem` dom su && 
    not (occurs t e)
    = let su' = su `catSubst` [(t, e)] in
      (su', sub su' e)
unifyTerms su e (EffVar (Eff t))
  | t `notElem` dom su && 
    not (occurs t e)
    = let su' = su `catSubst` [(t, e)] in
      (su', sub su' e)
unifyTerms su (AppEff (EffVar (Eff t)) (EffVar (Src x))) e'
  | t `notElem` dom su
  = let su' = su `catSubst` [(t, AbsEff (Src x) e')] in
    (su', sub su e')
unifyTerms su e' (AppEff (EffVar (Eff t)) (EffVar (Src x)))
  | t `notElem` dom su
  = let su' = su `catSubst` [(t, AbsEff (Src x) e')] in
    (su', sub su e')
unifyTerms su (AbsEff (Src s) e) (AbsEff (Src s') e')
  = let (su', t') = unifyTerms su (sub [(s, s')] e) e' in
    (su', AbsEff (Src s') t')
unifyTerms su (AbsEff (Eff s) e) (AbsEff (Eff s') e')
  | s == s'
    = let (su', t') = unifyTerms su e e' in
    (su', AbsEff (Eff s') t')
unifyTerms su (AppEff m n) (AppEff m' n')
  = let (su', m'')  = unifyTerms su m m'
        (su'', n'') = unifyTerms su' (sub su' n) (sub su' n')
    in  (su'', AppEff m'' n'')
unifyTerms su (Pend e s) (Pend e' s')
  = let (su, e'') = unifyTerms su e e' in
    (su, Pend e'' s)
unifyTerms su (Pend e s) e'
  = unifyTerms su e e'
unifyTerms su e (Pend e' s)
  = unifyTerms su e e'
unifyTerms su (NonDet es) (NonDet es')
  = (su', NonDet es')
    where
      (su', es') = L.foldr go (su, []) (zip es es')
      go (e,e') (su, es) = let (su', e'') = unifyTerms su e e' in
                           (su', e'':es)
unifyTerms sub e@(EffVar x) (EffVar y)
  | x == y
  = (sub, e) -- should probably check these are the same!!!!
unifyTerms sub t@(EffLit t1) (EffLit t2)
  = (sub, t)
unifyTerms su (Bind m1 n1) (Bind m2 n2)
  = let (su', m)  = unifyTerms su m1 m2
        (su'', n) = unifyTerms su' (sub su' n1) (sub su' n2)
    in (su'', Bind m n)
unifyTerms sub t1 t2
  = error oops  -- (printEff t1) (printEff t2))
  where
    oops :: String
    oops = (printf "%s unifyTerm %s" (printEffTerm t1) (printEffTerm t2))

occurs :: Symbol -> Effect -> Bool
occurs s e
  = s `elem` freeEffTermVars (EffTerm e)

fst3 (x,_,_) = x
snd3 (_,y,_) = y
thd3 (_,_,z) = z           
-- This isn't right!!!!
joinEffects _ []
  = return noEff
joinEffects _ [(_,_,e)]
  = return e
joinEffects _ es@((_,_,EffNone):_)
  = if length es /= length ets
             then foldM unifyTysM EffNone ets
               -- error (printf "Some are not none! %s" (concat (printEff <$> es)))
             else return EffNone
  where
    ets = [ e | e@EffNone <- thd3 <$> es ]
joinEffects c es@((_,_,EffTerm _):_)
  = return . EffTerm . callCC
                     . withPid
                     $ if length ets /= length es
                       then error "Bad!"
                       else NonDet ets
    where
      ets = [ go e | e@(_,_,EffTerm _) <- es ]
      app e = AppEff (AppEff e (EffVar kont)) (EffVar me)
      go (x,y,EffTerm z) = Assume c (x,y) (betaReduce (app z))
  -- = EffTerm $ if length ets /= length es
  --             then error "Bad!"
  --             else NonDet ets
  --   where
  --     ets = [ e | EffTerm e <- es ]
  --     app e = AppEff (AppEff e (EffVar kont)) (EffVar me)
joinEffects c (e:es)
  = do foldM_ (\et e -> unifyTysM et (thd3 e)) (thd3 e) es
       joinEffects c =<< mapM (\(x,y,z) -> applySubstM z >>= \t -> return (x,y,t)) (e:es) 

printTy :: String -> SpecType -> EffectM()
printTy msg t
  = do emb <- gets tyconEmb
       liftIO $ print (msg ++ " " ++ showpp (rTypeSortedReft emb t))

lookupSpecType :: CoreExpr -> EffectM SpecType
lookupSpecType e@(Var x)
  = substa reintern <$> lookupType (getSrcSpan x) e
  -- = ((flip meet (uTop $ exprReft (symbol x))) <$>) <$> lookupType (getSrcSpan x) e
lookupSpecType (Tick tt e@(Var x))
  = substa reintern <$> lookupType (getSrcSpan x) e 
lookupSpecType (Tick tt e)
  = substa reintern <$> lookupType (tickSrcSpan tt) e
lookupSpecType e
  = return (ofType (CoreUtils.exprType e))

reintern s = symbol (symbolString s)
    
lookupType :: SrcSpan -> CoreExpr -> EffectM SpecType
lookupType s e = do
  ann <- gets annots
  case H.lookup s ann of
    Nothing  -> return (ofType (CoreUtils.exprType e)) -- error ("uhg oh" ++ show s)
    Just [t] -> return t

dbgTy :: String -> EffTy -> EffectM EffTy
dbgTy m t = liftIO (putStrLn (printf "%s: %s" m (printEff t))) >> return t

dbgSubst :: String -> EffectM ()
dbgSubst m = do
  tsu <- gets tsubst
  esu <- gets esubst
  liftIO (putStrLn (printf "%s %s %s" m (printSubst printEff tsu) (printSubst printEffTerm esu)))
            
printSubst :: (a -> String) -> [(Symbol, a)] -> String
printSubst f = concatMap go
  where
    go (x,y) = printf "[%s := %s]" (symbolString x) (f y)
