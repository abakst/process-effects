-- module Control.Process.MessagePassing.Effects ( synthEffects ) where
module Control.Process.MessagePassing.Effects  where

import Debug.Trace
import Data.Maybe
import Data.Monoid
import Data.List as L
import Data.HashMap.Strict as H
import Data.Map.Strict as M
import Control.Monad.State
import Text.PrettyPrint.HughesPJ hiding ((<>))
import Text.Printf
import System.IO.Unsafe

import GHC
import Id
import Var
import Type
import DataCon
import Name
import OccName
import CoreSyn hiding (collectArgs)
import CoreUtils
import PrelNames
import HscTypes hiding (lookupType)
import Annotations
import UniqFM
import Serialized
import IdInfo

import Control.Process.MessagePassing.GHCInterface
import Control.Process.MessagePassing.EffectTypes  
import Control.Process.MessagePassing.EffEnv
import Control.Process.MessagePassing.Builtins
import Control.Process.MessagePassing.Promela
import Control.Process.MessagePassing.PrettyPrint
import Control.Process.MessagePassing.Parse

import Language.Haskell.Liquid.Types hiding (target)
import Language.Haskell.Liquid.Transforms.CoreToLogic (mkLit)
import Language.Haskell.Liquid.Types.Literals
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Plugin as P hiding (target)
import Language.Haskell.Liquid.GHC.Misc

import Language.Fixpoint.Types hiding (PPrint(..), SrcSpan(..), ECon) 
import qualified Language.Fixpoint.Types as Fp

debugUnify = True
debugApp   = True

debug s x = trace (s ++ ": " ++ show x) x  

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

type Obligation = Doc
synthEffects :: EffEnv SpecType -> [CoreBind] -> EffectM (Maybe Obligation)
synthEffects g []
  = do case lookupString g "main" of
         Just e ->  return $ Just (promela e)
         Nothing -> return Nothing
synthEffects g (cb:cbs)
  = do ann <- gets annots
       g' <- synth1Effect g cb
       synthEffects g' cbs

synth1Effect :: EffEnv SpecType -> CoreBind -> EffectM (EffEnv SpecType)
synth1Effect g (NonRec b e)
  = do (et, p)  <- synthEff g e
       et       <- applySubstM et
       g'  <-  mapM applySubstBinding g
       let egen = generalizeEff g' (betaReduceTy et)
       liftIO $ putStrLn (printf "%s : %s %s" (symbolString . symbol $ b) (printEff egen) (showpp p)) 
       let tys = L.nub . tyInfos $ snd <$> tyBoundTys egen
       return (extend g' b egen p)

synth1Effect g (Rec [(b,e)])              
  = do et1      <- defaultEff (CoreUtils.exprType e)
       (et2, p) <- synthEff (extend g b et1 Nothing) e
       et       <- unifyTysM et1 et2
       g'       <- mapM applySubstBinding g
       let egen = generalizeEff g' (betaReduceTy et)
       liftIO $ putStrLn (printf "%s : %s %s" (symbolString . symbol $ b) (printEff egen) (showpp p))
       return (extend g' b egen p)

bkFun :: Type -> Maybe ([TyVar], [Type], Type)
bkFun t
  = if Type.isFunTy tfun then Just (tvs, targs', tout) else Nothing
  where
    (tvs, tfun)   = splitForAllTys t
    (targs, tout) = splitFunTys tfun
    targs'        = [ t | t <- targs, isArg t ]
    isArg t
      | isDictTy t     = False
      | isDictLikeTy t = case splitTyConApp_maybe t of
                           Just (tc, tys) -> L.null tys
                           _ -> False
      | otherwise      = True
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
                 return $ EPi x t' (abstractArg x Nothing t)
            

defaultEff :: Type -> EffectM EffTy
defaultEff t
  | isJust (bkFun t) = funTemplate t
defaultEff t
  = go =<< isEffectType t
  where
    go True = EffTerm <$> EffVar <$> (Eff <$> freshEffVar)
    go _    = return noEff

funTemplate :: Type -> EffectM EffTy
funTemplate t
  = do is <- mapM (const freshInt) tvs
       let evs    = zip tvs (sym <$> is)
           sym    = symbol . ("E" ++) . show
       funTemplate' evs [] t
  where
    Just (tvs, targs, tout) = bkFun t

default' evs xs t                              
  | isJust (bkFun t) = funTemplate' evs xs t
  | isTyVarTy t      = return $ go (fromJust (getTyVar_maybe t))
  | otherwise        = do isEff <- isEffectType t
                          if isEff then
                            mkOutEff xs
                          else
                            return noEff
  where
    go tv = maybe noEff ETyVar $ L.lookup tv evs
    mkOutEff xs = do
      eff <- EffVar <$> Eff <$> freshEffVar
      return . EffTerm $ L.foldl (\e1 -> AppEff e1 . EffVar . flip Src (Just t)) eff xs

funTemplate' evs xs t                    
   = mkPi evs [] (targs ++ [tout])
  where
    Just (_, targs, tout) = bkFun t
    mkPi evs xs [t]
      = default' evs xs t
    mkPi evs xs (t1:ts)
      = do x     <- freshTermVar
           e1    <- default' evs xs t1
           e2    <- mkPi evs (xs ++ [x]) ts
           return (EPi x e1 (abstractArg x (Just t1) e2))

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

synthEff :: EffEnv SpecType -> CoreExpr -> EffectM (EffTy, Maybe SpecType)
synthEff g e@(Var x)
  = do effEnv     <- First        <$> lookupEffTy g x
       builtinEff <- First        <$> builtinEffect x
       def        <- First . Just <$> defaultEff (CoreUtils.exprType e)
       r          <- First        <$> lookupAssm x
       envreft    <- First        <$> lookupReft g x
       reft0      <- First . Just <$> lookupSortedReft e
       let eff  = fromMaybe err . getFirst $ effEnv <> builtinEff <> def
           reft = fromMaybe err . getFirst $ envreft <> reft0
       liftIO $ putStrLn (printf "%s ::: %s %s\n" (Fp.showpp (symbol x)) (Fp.showpp (getFirst r)) (Fp.showpp reft))
       eff <- freshFnEff eff
       return (eff, Just reft)
  where
    err = error $ printf "Can't find an eff for %s" (symbolString (symbol x))
synthEff g eff@(Tick _ e)
  = do (et, p) <- synthEff g e
       reft    <- lookupSortedReft eff
       liftIO $ putStrLn (printf "tick reft is %s\n" (showpp reft))
       return (et, p `meetTys` Just reft)
-- synthEff g e@(App e1 e2)
--   = undefined -- synthApp g e x
  -- where
  --   es = unfoldApp e
-- synthEff g (App e@(Var f) (Type x))
--   = do isEff <- isEffectType x
--        if isEff then
--          do eff <- builtinClassEffect f
--             maybe (synthEff g e) freshFnEff eff
--        else
--          synthEff g e
synthEff g e@(App _ (Type _))
  = do (et, p) <- synthTyApps g e []
       reft <- lookupSortedReft e
       liftIO $ putStrLn (printf "ty app reft is %s\n" (showpp reft))
       return (et, p)
  where
    skip t
      | isDictTy t     = True
      | isDictLikeTy t = case splitTyConApp_maybe t of
                           Just (tc, tys) -> not (L.null tys)
                           _ -> True
      | otherwise      = False
    lift e = return (e, Nothing)
    synthTyApps g e'@(Var f) ts
      = do meff <- builtinClassEffect f (L.reverse ts)
           maybe (synthEff g e') ((lift =<<) . freshFnEff) meff
    synthTyApps g (App e (Type t)) ts
      = synthTyApps g e (t:ts)
    synthTyApps g (App e x) ts
      | skip (CoreUtils.exprType x)
      = synthTyApps g e ts
    synthTyApps g (Tick _ e) ts
      = synthTyApps g e ts
synthEff g eff@(App e m)
  | not (isTypeArg m) && skip (CoreUtils.exprType m)
  = do (et, p) <- synthEff g e
       reft <- lookupSortedReft eff
       liftIO $ putStrLn (printf "skip app reft is %s\n" (showpp reft))
       return (et, p)
  where
    skip t
      | isDictTy t     = True
      | isDictLikeTy t = case splitTyConApp_maybe t of
                           Just (tc, tys) -> not (L.null tys)
                           _ -> True
      | otherwise      = False
synthEff g (Lit l)
  = do  emb  <- gets tyconEmb 
        let reft = uRType $ literalFRefType l
        return $ (noEff, Just reft)
synthEff g (Let b e)
  = do g' <- synth1Effect g b
       synthEff g' e
synthEff g (Lam b e)
  | isTyVar b
  = synthEff g e
  | otherwise
  = do arge   <- defaultEff ty
       (te,_) <- synthEff (extend g b arge Nothing) e
       arge'  <- applySubstM arge
       return (EPi (symbol b) arge' (abstractArg (symbol b) (Just ty) (betaReduceTy te)), Nothing)
  where ty = varType b
synthEff g eff@(App eFun eArg)
  = do (funEff,funTy)             <- applySubstBinding =<<
                                     synthEff g eFun
       liftIO $ putStrLn (printf "funReft: %s\n" (Fp.showpp funTy))
       when debugApp $ (traceTy "funEff" funEff >> return ())
       (argEff, reft0)            <- applySubstBinding =<<
                                     synthEff g eArg
       liftIO $ putStrLn (printf "argReft: %s\n" (Fp.showpp reft0))
       reft2 <- lookupSortedReft eff
       let reft    = fromMaybe reft2 reftapp
           reftapp = applyRefts funTy eArg reft0
       liftIO $ case maybeExtractVar eArg of
                  Just x -> putStrLn (printf "trying %s ====> %s\n" (symbolString x) (Fp.showpp reftapp))
                  Nothing -> return ()
       when debugApp $ (traceTy "argEff" argEff >> return ())
       v                          <- freshTermVar
       let x = maybe v id $ maybeExtractVar eArg
       e                          <- freshEffTyVar
       -- unifyTysM tIn argEff
       EPi s tIn tOut             <- applySubstM =<< unifyTysM funEff (EPi v argEff e)
       -- reft                       <- lookupSortedReft eArg
       effOut                     <- applySubstM tOut
       liftIO $ putStrLn (printf "app return reft is %s\n" (Fp.showpp reft))
       let effOutSub = maybeSubArg x reft0 $ applyArg x mty Nothing {- reft -} effOut
       liftIO $ putStrLn (printf "apply %s\n\t%s\n\tx:%s\n\ts:%s\n\treft: %s "
                                     (printEff (betaReduceTy effOut))
                                     (printEff (betaReduceTy $ effOutSub))
                                     (symbolString x) (symbolString s) (showpp reft))
       -- liftIO $ putStrLn (printf "envout %s\n" (Fp.showpp (assocs (snd <$> g))))
       return (effOutSub, Just reft)
  where
    mty = Just ty
    maybeSubArg :: Symbol -> Maybe SpecType -> EffTy -> EffTy
    maybeSubArg s (Just t) e
      -- = maybe e (\v -> sub [(s, Info (v,ty,t))] e) $ maybeExtractVar eArg
      = maybe e (\v -> prefixInfo (Info  v ty t env) $ sub [(s, Info v ty t env)] e) $ maybeExtractVar eArg
    maybeSubArg _ _ e
      = e
    env = snd <$> g 
    ty = CoreUtils.exprType eArg

synthEff g (Case e x t alts)
  = do es <- mapM (altEffect g) alts
       reft <- lookupSortedReft e
       -- assume EffTerms...
       eff <- betaReduceTy <$> joinEffects g (symbol ex) (CoreUtils.exprType e) reft es
       return (eff, Nothing)
  where
    app e = AppEff (AppEff e (EffVar kont)) (EffVar me)
    ex = maybe err id $ maybeExtractVar e
    err = error "Not a var (case)"

applyRefts :: Maybe SpecType -> CoreSyn.Expr b -> Maybe SpecType -> Maybe SpecType
applyRefts (Just ft) (Lit l) xt
  | (_, _, _, f)        <- bkUniv ft,
    (_, RFun x t t' _)  <- bkClass f
  = Just $ subst1 (substa reintern t') (reintern x, fromJust $ mkLit l)
applyRefts (Just ft) (Var x') xt
  | (_, _, _, f)        <- bkUniv ft,
    (_, RFun x t t' _)  <- bkClass f
  = Just $ subst1 (substa reintern t') (reintern x, expr (symbol x'))
applyRefts ft (Tick tt e) xt
  = applyRefts ft e xt
applyRefts ft l xt
  = Nothing

meetTys :: Maybe SpecType -> Maybe SpecType -> Maybe SpecType     
meetTys (Just t) (Just t')
  = Just (t `strengthen` ofReft r)
  where
    r = rTypeReft t `meet` rTypeReft t'
meetTys (Just t) t' = Just t
meetTys _ t'        = t'

prefixInfo :: Info -> EffTy -> EffTy
prefixInfo i = go 
  where
    go EffNone        = EffNone
    go (EForAll x t)  = go t
    go (ETyApp e1 e2) = ETyApp (go e1) (go e2)
    go (EPi s t1 t2)  = EPi s t1 (go t2)
    go (EffTerm e)    = EffTerm (Pend e i)

generalizeEff :: EffEnv SpecType -> EffTy -> EffTy
generalizeEff g
  = gen freeEffTyVars EForAll . gen freeEffTermVars ETermAbs
  where
    gen f c t
      = L.foldr go t free 
      where
        go s t = c s t
        free = fvs L.\\ gvs
        fvs = f t
        gvs = nub (concatMap (f . fst) $ bindings g)

altEffect :: EffEnv SpecType -> CoreAlt -> EffectM (DataCon, [Symbol], EffTy)
altEffect g (DataAlt dc, bs, e)
  = do (t, _) <- synthEff g e
       return (dc, symbol <$> bs, t)
altEffect g (LitAlt _, _, e)
  = return $ (error "LitAlt", [], noEff)
altEffect g (DEFAULT, _, _)
  = return $ (error "DEFAULT", [], noEff)

maybeExtractVar (Var v)     = Just (symbol v)
maybeExtractVar (Tick tt e) = maybeExtractVar e
maybeExtractVar _           = Nothing

applySubstM :: EffTy -> EffectM EffTy                              
applySubstM t
  = do tsu <- gets tsubst
       esu <- gets esubst
       return (sub esu (sub tsu t))

applySubstBinding :: (EffTy, Maybe r) -> EffectM (EffTy, Maybe r)              
applySubstBinding (e, p)
  = do e' <- applySubstM e
       return (e', p)

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
  = do u@(_,_,t) <- unifyTermTys tsu esu t1 t2
       when debugUnify . liftIO $ do (putStrLn dbg)
                                     (putStrLn (printf "===> %s\n" (printEff t)))
       return u
  where
    dbg = printf "UNIFY:\n%s\n%s\n\n\tsubt:(%s)\n\tsube:(%s)"
            (printEff t1) (printEff t2)
            (printSubst printEff tsu) (printSubst printEffTerm esu)

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
       (tSub2, eSub2, tyOut) <- unifyTys tSub1 eSub1 (ap $ sub [(s,v)] (applyArg v Nothing Nothing t2))
                                                     (ap $ sub [(s',v)] (applyArg v Nothing Nothing t2'))
       return (sub eSub2 (sub eSub1 tSub2), eSub2, EPi v tyIn (abstractArg v Nothing tyOut))
unifyTermTys tSub eSub (ETermAbs s t) (ETermAbs s' t')
  = do e         <- freshEffVar
       let inst  = [(s, EffVar (Eff e)), (s', EffVar (Eff e))]
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

unifyTerms su e1 e2
  = (su', t')
  where
    t'      = if debugUnify then tracepp "unifyTerms(res)" t else t
    e1'     = if debugUnify then tracepp "unifyTerms(e1)" e1 else e1
    e2'     = if debugUnify then tracepp "unifyTerms(e2)" e2 else e2
    (su',t)  = unifyTerms' su e1' e2'
    tracepp = Control.Process.MessagePassing.Promela.tracepp

unifyTerms' su (Pend e s) (Pend e' s')
  = let (su', e'') = unifyTerms su e e' in
    (su', Pend e'' s')
-- unifyTerms' su (Pend e s) e'
--   = let (su', e'') = unifyTerms su e e' in
--     (su', sub su' (Pend e'' s))
-- unifyTerms' su e (Pend e' s)
--   = let (su', e'') = unifyTerms su e e' in
--     (su', sub su' (Pend e'' s))
unifyTerms' su (EffVar (Eff t)) e
  | t `notElem` dom su && 
    not (occurs t e)
    = let su' = su `catSubst` [(t, e)] in
      (su', sub su' e)
unifyTerms' su e (EffVar (Eff t))
  | t `notElem` dom su && 
    not (occurs t e)
    = let su' = su `catSubst` [(t, e)] in
      (su', sub su' e)
unifyTerms' su e1@(AppEff (EffVar v) _) e2
  | Just (su', e') <- unifyApply su e1 e2
  = (su', e')
unifyTerms' su e1 e2@(AppEff (EffVar v) _)
  | Just (su', e') <- unifyApply su e1 e2
  = (su', e')
-- unifyTerms' su e@(AppEff (EffVar (Eff t)) e1) 
--                  (AppEff (EffVar (Eff u)) e2)
--   | t == u 
--   = (su, e)
unifyTerms' su (AppEff (EffVar (Eff t)) (EffVar (Src x ty))) e'
  | t `notElem` dom su &&
    not (occurs t e')
  = let su' = su `catSubst` [(t, AbsEff (Src x ty) e')] in
    (su', sub su e')
unifyTerms' su e' (AppEff (EffVar (Eff t)) (EffVar (Src x ty)))
  | t `notElem` dom su &&
    not (occurs t e')
  = let su' = su `catSubst` [(t, AbsEff (Src x ty) e')] in
    (su', sub su e')

-- -- Need to generalize this (should be easy)
-- unifyTerms' su e' (AppEff ((AppEff (EffVar (Eff t)) (EffVar (Src x ty)))) (EffVar (Src x' ty')))
--   | t `notElem` dom su &&
--     not (occurs t e')
--   = let su' = su `catSubst` [(t, (AbsEff (Src x ty) (AbsEff (Src x' ty') e')))] in
--     (su', sub su' e')
-- unifyTerms' su (AppEff ((AppEff (EffVar (Eff t)) (EffVar (Src x ty)))) (EffVar (Src x' ty'))) e'
--   | t `notElem` dom su &&
--     not (occurs t e')
--   = let su' = su `catSubst` [(t, (AbsEff (Src x ty) (AbsEff (Src x' ty') e')))] in
--     (su', sub su' e')

unifyTerms' su e1 e2
  | Just (su, e) <- unifyRecursive su e1 e2
  = (su, e)
unifyTerms' su (AbsEff (Src s ty) e) (AbsEff (Src s' ty') e')
  | isNothing ty || isNothing ty' || ty == ty'
  = let (su', t') = unifyTerms su (sub [(s, s')] e) e'
        ty'' = getFirst (First ty <> First ty')
    in (su', AbsEff (Src s' ty'') t')
unifyTerms' su (AbsEff (Eff s) e) (AbsEff (Eff s') e')
  | s == s'
    = let (su', t') = unifyTerms su e e' in
    (su', AbsEff (Eff s') t')
unifyTerms' su (AppEff m n) (AppEff m' n')
  = let (su', m'')  = unifyTerms su m m'
        (su'', n'') = unifyTerms su' (sub su' n) (sub su' n')
    in  (su'', AppEff m'' n'')
unifyTerms' su (NonDet es) (NonDet es')
  = (su', NonDet es')
    where
      (su', es') = L.foldr go (su, []) (zip es es')
      go (e,e') (su, es) = let (su', e'') = unifyTerms su e e' in
                           (su', e'':es)
unifyTerms' sub e@(EffVar x) (EffVar y)
  | symbol x == symbol y
  = (sub, e) -- should probably check these are the same!!!!
unifyTerms' sub t@(EffLit t1) (EffLit t2)
  = (sub, t)
unifyTerms' su (Bind m1 n1) (Bind m2 n2)
  = let (su', m)  = unifyTerms su m1 m2
        (su'', n) = unifyTerms su' (sub su' n1) (sub su' n2)
    in (su'', Bind m n)
unifyTerms' sub t1 t2
  = error oops
  where
    oops :: String
    oops = (printf "%s unifyTerm %s" (printEffTerm t1) (printEffTerm t2))

unifyApply su (AppEff m n) (AppEff m' n')            
  = Just (su'', AppEff m'' n'')
  where
    (su', m'') = unifyTerms su m m'
    (su'', n'') = unifyTerms su' n n'
unifyApply su e@(AppEff m n) e'
  | (EffVar (Eff f), as) <- unwrapApply e,
    (xs, [])             <- collectArgs as,
    f `notElem` dom su && not (occurs f e')
  = let fun = L.foldr AbsEff e' (trace "xs" xs)
        su' = su `catSubst` [(f, fun)]
    in Just (su', fun)
-- unifyApply su e e'@(AppEff m n)
--   = unifyApply su e' e
unifyApply _ _ _
  = Nothing

unifyRecursive su e@(AppEff m n) e'
  -- | (EffVar (Eff f), as)   <- unwrapApply e,
  --   (EffVar (Eff f'), as') <- unwrapApply e',
  --   f == f'
  -- = Nothing
  | (EffVar (Eff f), as) <- unwrapApply e,
    (xs, [])             <- collectArgs as, 
    f `notElem` dom su && occurs f e'
  = let su'  = su `catSubst` mu
        body = L.foldr AbsEff e' xs
        mu   = [(f, Mu f body)]
    in Just $ (su', L.foldl AppEff (Mu f body) (EffVar <$> xs))
unifyRecursive _ _ _
  = Nothing

collectArgs :: [Effect] -> ([Binder], [Effect])
collectArgs = go []
  where
    go xs (EffVar x@(Src _ _):xs') = go (x:xs) xs'
    go xs ((Pend e i):xs')
      | Just x <- extract e = go (x:xs) xs'
    go xs xs'                      = (reverse xs, xs')
    extract (Pend e i)           = extract e
    extract (EffVar x@(Src _ _)) = Just x
    extract _                    = Nothing

-- unifyTerms su (AppEff (EffVar (Eff t)) (EffVar (Src x ty))) e'
--   | t `notElem` dom su
--   = let su' = su `catSubst` mu
--         bdy = AbsEff (Src x ty) e'
--         mu  = [(t, Mu t bdy)]
--     in (su', AppEff (Mu t bdy) (EffVar (Src x ty)))

-- This isn't right!!!!
joinEffects _ _ _ _ []
  = return noEff
joinEffects _ _ _ _ es@((_,_,EffNone):_)
  = if length es /= length ets
             then foldM unifyTysM EffNone ets
               -- error (printf "Some are not none! %s" (concat (printEff <$> es)))
             else return EffNone
  where
    ets = [ e | e@EffNone <- thd3 <$> es ]
joinEffects env c ty t es@((_,_,EffTerm _):_)
  = return . EffTerm . callCC
                     . withPid
                     $ if length ets /= length es
                       then error "Bad!"
                       else NonDet ets
    where
      g   = snd <$> env
      ets = [ go e | e@(_,_,EffTerm _) <- es ]
      app e = AppEff (AppEff e (EffVar kont)) (EffVar me)
      go (x,y,EffTerm z) = Assume (Info c ty t g) (x,y) (betaReduce (app z))
joinEffects env c ty t (e:es)
  = do foldM_ (\et e -> unifyTysM et (thd3 e)) (thd3 e) es
       joinEffects env c ty t =<< mapM (\(x,y,z) -> applySubstM z >>= \t -> return (x,y,t)) (e:es) 

printTy :: String -> SpecType -> EffectM ()
printTy msg p
  = liftIO $ print (msg ++ " " ++ showpp p)

lookupSortedReft :: CoreExpr -> EffectM SpecType
lookupSortedReft e@(Var x)
  = do t_spec  <- substa reintern <$> lookupType (getSrcSpan x) e
       t_spec' <- checkSpec e t_spec
       t_assm  <- lookupAssm x
       return $ fromMaybe t_spec' t_assm
lookupSortedReft (Tick tt e@(Var x))
  = checkSpec e =<< substa reintern <$> lookupType (getSrcSpan x) e 
lookupSortedReft (Tick tt e)
  = checkSpec e =<< substa reintern <$> lookupType (tickSrcSpan tt) e
lookupSortedReft e
  = defaultSortedReft e
reintern s = symbol (symbolString s)

lookupAssm :: Var -> EffectM (Maybe SpecType)
lookupAssm x = L.lookup x <$> gets assms

checkSpec e tspec = do
   emb    <- gets tyconEmb
   t_def  <- defaultSortedReft e
   let (RR so _) = rTypeSortedReft emb tspec
   let (RR so' _) = rTypeSortedReft emb t_def
   return $ if so == so' then tspec
                         else t_def

defaultSortedReft :: CoreExpr -> EffectM SpecType
defaultSortedReft e
  = do emb <- gets tyconEmb
       let t = ofType (CoreUtils.exprType e) :: SpecType
       return t
    
lookupType :: SrcSpan -> CoreExpr -> EffectM SpecType
lookupType s e = do
  ann <- gets annots
  emb <- gets tyconEmb
  case H.lookup s ann of
    Nothing  ->
      let t = ofType (CoreUtils.exprType e) :: SpecType in
      return t
    Just [t] -> do
      return t

traceTy :: String -> EffTy -> EffectM EffTy
traceTy m t = liftIO (putStrLn (printf "%s: %s" m (printEff t))) >> return t

dbgSubst :: String -> EffectM ()
dbgSubst m = do
  tsu <- gets tsubst
  esu <- gets esubst
  liftIO (putStrLn (printf "%s %s %s" m (printSubst printEff tsu) (printSubst printEffTerm esu)))
            
printSubst :: (a -> String) -> [(Symbol, a)] -> String
printSubst f = concatMap go
  where
    go (x,y) = printf "[%s := %s]" (symbolString x) (f y)
