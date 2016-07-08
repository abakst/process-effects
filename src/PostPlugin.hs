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
betaReduceTy (EPi s e1 e2)
  = EPi s (betaReduceTy e1) (betaReduceTy e2)
betaReduceTy (ETermAbs s e)
  = ETermAbs s (betaReduceTy e)
betaReduceTy (EForAll s e)
  = EForAll s (betaReduceTy e)
betaReduceTy (ETyApp e1 e2)
  = ETyApp (betaReduceTy e1) (betaReduceTy e2)
betaReduceTy (EffTerm e)
  = EffTerm (betaReduce e)
betaReduceTy EffNone
  = EffNone

betaReduce :: Effect -> Effect
betaReduce (Nu b e) = Nu b (betaReduce e)
betaReduce (NonDet es) = NonDet (betaReduce <$> es)
betaReduce (Par e1 e2)
  = Par (betaReduce e1) (betaReduce e2)
betaReduce (Bind e1 e2)
  = Bind (betaReduce e1) (betaReduce e2)
betaReduce (AbsEff s e)
  = AbsEff s (betaReduce e)
betaReduce (AppEff e1 e2)
  = let e2' = betaReduce e2 in
    case betaReduce e1 of
      e1'@(AbsEff (Eff s) m) ->
        betaReduce $ sub [(s, e2')] m
      e1'@(AbsEff (Src s) m) ->
        case e2' of
          Pend (EffVar (Src v)) (x,t) ->
            betaReduce $ Pend (sub [(s, v)] m) (x,t)
          EffVar (Src v) ->
            betaReduce $ sub [(s, v)] m
          _ -> AppEff e1' e2'
      e1' -> AppEff e1' e2'
betaReduce (Pend e xt) = Pend (betaReduce e) xt
betaReduce (Assume s (c,bs) e) = Assume s (c,bs) (betaReduce e)
betaReduce e = e

freshInt = do n <- gets ctr
              modify $ \s -> s { ctr = n + 1}
              return n
freshEffVar = do n <- freshInt
                 return (symbol ("η" ++ show n))
freshTermVar = do n <- freshInt
                  return (symbol ("x" ++ show n))
freshChanVar = do n <- freshInt
                  return (symbol ("p" ++ show n))

freshFnEff :: EffTy -> EffectM EffTy
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
  = printf "(Π%s:%s. %s)" (symbolString s) (printEff e1) (printEff e2)
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
                        (EffTerm (effBindF
                                     (AppEff (EffVar (Eff e1Sym))
                                              (EffVar (Src xSym))))))
                 (EffTerm (effBindF
                              (AppEff (AppEff (EffVar (Eff e0Sym))
                                                (EffVar (Eff e1Sym)))
                                                (EffVar me))))
  where
    fSym = symbol "f"
    actSym = symbol "act"
    e0Sym = symbol "e0"
    e1Sym = symbol "e1"
    xSym = symbol "x"

thenEffectTy = ETermAbs e0Sym
             $ ETermAbs e1Sym
             $ EPi fSym (EffTerm (EffVar (Eff e0Sym)))
             $ EPi gSym (EffTerm (AbsEff kont (AbsEff me (EffVar (Eff e1Sym)))))
             $ EffTerm (effBindF (AppEff (AppEff (EffVar (Eff e0Sym))
                                              (AbsEff (Src (symbol "_")) (EffVar (Eff e1Sym))))
                              (EffVar me)))
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
  = do et <- synthEff g e 
       liftIO $ putStrLn (printf "%s : %s" (getOccString b) (printEff $ betaReduceTy et))
       return (M.insert (getName b) et g)

lookupEff :: EffEnv -> CoreExpr -> EffectM EffTy
lookupEff g e@(Var x)
  | isRecordSel x
    = return $ EPi (symbol "_") noEff noEff
  where
    isRecordSel x = case idDetails x of
                      RecSelId {} -> True
                      _ -> False
lookupEff g e@(Var x)
  = case M.lookup (getName x) g of
      Nothing -> do
        let t = CoreUtils.exprType e
        defaultEff (CoreUtils.exprType e)
      Just e  -> return e

bkFun :: Type -> Maybe ([TyVar], [Type], Type)
bkFun t
  = if Type.isFunTy tfun then Just (tvs, targs', tout) else Nothing
  where
    (tvs, tfun)   = splitForAllTys t
    (targs, tout) = splitFunTys tfun
    targs'        = [ t | t <- targs, not (isDictLikeTy t) ]

walkTyVars f t
  | isTyVarTy t
    = f (fromJust (getTyVar_maybe t))
  | otherwise 
    = case bkFun t of
        Just (tvs, ts, tout) ->
          let ets  = walkTyVars f <$> (ts ++ [tout])
          in L.foldr1 (EPi (symbol "_")) ets 
        Nothing ->
          noEff
                 
defaultEff :: Type -> EffectM EffTy
defaultEff t
  | isJust (bkFun t)
  = do is <- mapM (const freshInt) tvs
       let evs    = zip tvs (sym <$> is)
           sym    = symbol . ("E" ++) . show
           ets    = walkTyVars (go evs) <$> (targs ++ [tout])
           funTy  = L.foldr1 (EPi (symbol "_")) ets
       return funTy
  where
    Just (tvs, targs, tout) = bkFun t
    go evs tv = maybe noEff ETyVar $ L.lookup tv evs
defaultEff t
  | Type.isFunTy t
  = case splitFunTy_maybe t of
      Just (tin, tout) -> do
        return noEff
  | otherwise
  = return noEff

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
       -- liftIO $ putStrLn (symbolString (symbol x))
       -- liftIO $ putStrLn (show as)
       case as of
         [t] -> case parseEffTy t of
                  Right et -> return et
         _   -> lookupEff g e
synthEff g (Tick _ e)
  = synthEff g e
synthEff g (App e@(Var f) (Type x))
  = isEffectType x >>= lookupFunType
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
  | skip (CoreUtils.exprType m)
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
  = do te <- synthEff g e
       return (EPi (symbol b) noEff te)
synthEff g (App eFun eArg)
  = do funEff                     <- synthEff g eFun
       funEffFresh                <- freshFnEff funEff
       let EPi s freshIn freshOut = funEffFresh
       argEff                     <- synthEff g eArg
       tyArg                      <- lookupSpecType eArg
       tyIn                       <- unifyTysM argEff (maybeSubArg s tyArg freshIn)
       tyOut                      <- maybeSubArg s tyArg <$> applySubstM freshOut
       -- liftIO (putStrLn (printf "(%s => %s) %s" (printEff (maybeSubArg s tyArg freshIn)) (printEff (maybeSubArg s tyArg (sub tu' (sub eu' freshOut)))) (printEff (argEff))))
       return tyOut
  where
    maybeSubArg :: Symbol -> SpecType -> EffTy -> EffTy
    maybeSubArg s t e
      = maybe e (\v -> sub [(s, Info (v,t))] e) $ maybeExtractVar eArg

synthEff g (Case e x t alts)
  = do es <- mapM (altEffect g) alts
       -- assume EffTerms...
       betaReduceTy <$> joinEffects (symbol ex) es
  where
    app e = AppEff (AppEff e (EffVar kont)) (EffVar me)
    ex = maybe err id $ maybeExtractVar e
    err = error "Not a var (case)"

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
       return (sub tsu (sub esu t))

unifyTysM :: EffTy -> EffTy -> EffectM EffTy
unifyTysM t1 t2
  = do tsu <- gets tsubst
       esu <- gets esubst
       (tsu, esu, t) <- unifyTermTys tsu esu t1 t2
       modify $ \s -> s { tsubst = tsu, esubst = esu }
       return t

unifyTermTys tSub eSub EffNone EffNone
  = return (tSub, eSub, EffNone)
unifyTermTys tSub eSub (ETyVar t) t'
  | t `notElem` dom tSub
  = return (tSub `catSubst` [(t, t')], eSub, t')
unifyTermTys tSub eSub t' (ETyVar t)
  | t `notElem` dom tSub
  = return (tSub `catSubst` [(t, t')], eSub, t')
unifyTermTys tSub eSub (EffTerm t1) (EffTerm t2)
  = do let (eSub', t) = unifyTerms eSub t1 t2
       return (tSub, eSub', EffTerm t)
unifyTermTys tSub eSub f@(EPi s t1 t2) (EPi s' t1' t2')
  = do v                     <- freshTermVar
       (tSub1, eSub1, tyIn)  <- unifyTermTys tSub eSub (sub [(s,v)] t1) (sub [(s',v)] t1')
       (tSub2, eSub2, tyOut) <- unifyTermTys tSub1 eSub1 (sub [(s,v)] t2) (sub [(s',v)] t2')
       return (tSub2, eSub2, EPi v tyIn tyOut)
unifyTermTys tSub eSub (ETermAbs s t) (ETermAbs s' t')
  = do e         <- freshEffVar
       let inst  = [(s, EffVar (Eff e))]
       (tSub, eSub, t'') <- unifyTermTys tSub eSub (sub inst t) (sub inst t')
       return (tSub, eSub, ETermAbs e t'')
unifyTermTys tSub eSub t@(ETermAbs _ _) t'
  = do e <- freshEffVar
       unifyTermTys tSub eSub t (ETermAbs e t')
unifyTermTys tSub eSub t t'@(ETermAbs _ _)
  = do e <- freshEffVar
       unifyTermTys tSub eSub (ETermAbs e t) t'
unifyTermTys tsub esub t1 t2
  = error oops  -- (printEff t1) (printEff t2))
  where
    oops = printf "%s unify %s (%s) (%s)" (printEff t1) (printEff t2) (show tsub) (show esub)

unifyTerms su (EffVar (Eff t)) e
  | t `notElem` dom su
    = let su' = su `catSubst` [(t, e)] in
      (su', sub su' e)
unifyTerms su e (EffVar (Eff t))
  | t `notElem` dom su
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
unifyTerms sub t@(EffVar _) (EffVar _)
  = (sub, t) -- should probably check these are the same!!!!
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
