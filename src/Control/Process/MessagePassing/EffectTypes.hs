{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleInstances #-}
{-# Language DeriveDataTypeable #-}
module Control.Process.MessagePassing.EffectTypes (
    Binder(..)
  , Effect(..)
  , Info(..)
  , EffectM(..)
  , EffState(..)
  , EffTy(..)
  , EffectSubst(..)
  , betaReduceTy
  , betaReduce
  , applyArg, abstractArg
  , freeEffTyVars
  , freeEffTermVars
  , symbolString
  , symbol
  , dom
  , catSubst
  , Symbol(..)
  , freshInt, freshTermVar, freshEffVar, freshChanVar, freshEffTyVar
  , gets, modify
  , unwrapApply
  , occurs
  , localVars
  , fst3, snd3, thd3
  ) where

import Debug.Trace
import Data.Generics (Data, everything, mkQ)

import           Var
import           GHC
import           Annotations
import           Data.Function
import           Data.List
import qualified Data.HashMap.Strict as H
import qualified Data.Map.Strict as M
import           Control.Monad.Reader
import           Control.Monad.State
import           Text.Printf

import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.RefType
import           Language.Fixpoint.Types hiding (SrcSpan(..), ECon, filterSubst, catSubst) 
  
debug s x = trace (s ++ ": " ++ show x) x  
data Binder = Src Symbol (Maybe Type)
            | Eff Symbol
              deriving (Eq, Data)

data Info = Info { infoSym  :: Symbol
                 , infoTy   :: Type
                 , infoReft :: SpecType
                 , infoEnv  :: M.Map Var (Maybe SpecType)
                 }
  deriving (Data)

data Effect = EffLit String
            | AppEff Effect Effect
            | AbsEff Binder Effect
            | EffVar Binder
            | Bind Effect Effect
            | NonDet [Effect]
            | Nu Symbol Effect
            | Mu Symbol Effect
            | Par Effect Effect
            | Assume Info (DataCon, [Symbol]) Effect
            | Pend Effect Info
              deriving (Data)

data EffTy  = EPi Symbol EffTy EffTy 
            | EForAll Symbol EffTy
            | ETyVar Symbol
            | ETermAbs Symbol EffTy
            | ETyApp EffTy EffTy
            | EffTerm Effect
            | EffNone
              deriving (Data)

data EffState = EffState {
    ctr      :: Int
  , annots   :: H.HashMap SrcSpan [SpecType]
  , hsenv    :: HscEnv
  , assms    :: [(Var, SpecType)]
  , annenv   :: AnnEnv
  , tyconEmb :: TCEmb TyCon
  , tsubst   :: [(Symbol, EffTy)]
  , esubst   :: [(Symbol, Effect)]
  , target   :: ModuleName
  }
type EffectM a = StateT EffState IO a

freshInt :: EffectM Int
freshInt =
  do n <- gets ctr
     modify $ \s -> s { ctr = n + 1}
     return n
freshEffVar =
  do n <- freshInt
     return (symbol ("f" ++ show n))
freshTermVar
  = do n <- freshInt
       return (symbol ("x" ++ show n))
freshChanVar
  = do n <- freshInt
       return (symbol ("p" ++ show n))
freshEffTyVar
  = do n <- freshInt
       return (ETyVar (symbol ("E" ++ show n)))

betaReduceTy :: EffTy -> EffTy
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
betaReduceTy e@(ETyVar _)
  = e
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
betaReduce (Mu s e)
  = Mu s (betaReduce e)
betaReduce (AppEff (Pend e1 i) e2)
  = Pend (betaReduce (AppEff e1 e2)) i
betaReduce (AppEff e1 (Pend e2 i))
  = Pend (betaReduce (AppEff e1 e2)) i
betaReduce (AppEff e1 e2)
  = case (betaReduce e1, betaReduce e2) of
      (AbsEff (Eff s) m, n) ->
        betaReduce $ sub [(s, n)] m

      (AbsEff (Src s ty) m, EffVar (Src s' ty')) ->
        betaReduce $ sub [(s, s')] m

      (AbsEff (Src s ty) m, n) ->
        betaReduce $ sub [(s, n)] m

      (Pend e1' i, e2') -> Pend (betaReduce (AppEff e1' e2')) i
      (e1', e2') -> AppEff e1' e2'
betaReduce (Pend e xt) = Pend (betaReduce e) xt
betaReduce (Assume i (c,bs) e) = Assume i (c,bs) (betaReduce e)
betaReduce e = e


applyArg :: Symbol -> Maybe Type -> Maybe Info -> EffTy -> EffTy
applyArg x mt mi = go
  where
    go EffNone           = EffNone
    go (EForAll x' t)    = t -- WRONG
    go (ETyApp e1 e2)    = ETyApp (go e1) (go e2)
    go (EPi s' t1' t2')  = EPi s' (go t1') (go t2')
    go (EffTerm e)       = EffTerm (betaReduce $ AppEff e m)
      where
        m = maybe v (Pend v) mi
        v = EffVar (Src x mt)
    go e = e

abstractArg :: Symbol -> Maybe Type -> EffTy -> EffTy
abstractArg x t = go
  where
    go EffNone           = EffNone
    go (EForAll s t)     = EForAll s (go t)
    go (ETyApp e1 e2)    = ETyApp (go e1) (go e2)
    go (EPi s' t1' t2')  = EPi s' (go t1') (go t2')
    go (EffTerm e)       = EffTerm (AbsEff (Src x t) e)
    go e                 = {- EForAll x -} e

-- SO BAD, PLEASE REFACTOR ME!!!
freeEffTyVars :: EffTy -> [Symbol]                       
freeEffTyVars (EPi s t1 t2)
  = collect freeEffTyVars t1 t2
freeEffTyVars (EForAll s t)
  = freeEffTyVars t \\ [s]
freeEffTyVars (ETyVar s)
  = [s]
freeEffTyVars (ETermAbs s t)
  = freeEffTyVars t
freeEffTyVars (ETyApp t1 t2)
  = collect freeEffTyVars t1 t2
freeEffTyVars _
  = []

collect f x y
  = nub (f x ++ f y)

freeEffTermVars :: EffTy -> [Symbol]    
freeEffTermVars (EffTerm e)
  = go e
  where
    go (AppEff e1 e2)      = collect go e1 e2 
    go (AbsEff (Src _ _) e2) = go e2
    go (AbsEff (Eff x) e2) = go e2 \\ [x]
    go (Bind e1 e2)        = collect go e1 e2
    go (NonDet es)         = nub (concatMap go es)
    go (Nu _ e)            = go e
    go (Mu x e)            = go e \\ [x]
    go (Par e1 e2)         = collect go e1 e2
    go (Assume _ _ e)      = go e
    go (Pend e _)          = go e
    go (EffVar (Eff x))    = [x]
    go _                   = []
freeEffTermVars (EPi s t1 t2)
  = collect freeEffTermVars t1 t2
freeEffTermVars (EForAll s t)
  = freeEffTermVars t
freeEffTermVars (ETermAbs s t)
  = freeEffTermVars t \\ [s]
freeEffTermVars (ETyApp t t')
  = collect freeEffTermVars t t'
freeEffTermVars _ = []

instance Symbolic Binder where
  symbol (Src x _) = x
  symbol (Eff x)   = x
                   
filterSubst f su
  = [ (x,y) | (x,y) <- su, f x y ]

catSubst :: EffectSubst a a => [(Symbol, a)] -> [(Symbol, a)] -> [(Symbol, a)]
catSubst su1 su2
  = sub su2 su1 ++ filterSubst uniq su2
  where
    uniq k _ = k `notElem` dom su1


class EffectSubst a b where
  sub :: [(Symbol, a)] -> b -> b

instance EffectSubst a b => EffectSubst a (Symbol, b) where
  sub su (s, x) = (s, sub su x)
    -- case lookup s su of
    --   Just x' -> (s, x')
    --   Nothing -> (s, x)

instance EffectSubst a b => EffectSubst a [b] where
  sub su = (sub su <$>)

instance EffectSubst Symbol EffTy where
  sub su = genericSubstTy (const ETyVar) go goInfo fixSubst su
    where
      go (Src _ t) s = EffVar (Src s t)
      go (Eff _) s   = EffVar (Eff s)
      goInfo su (x,t)
        = withMatch su x (x, fixSubst su $ t) (\_ s' -> (s', fixSubst su t))

fixSubst :: Subable a => [(Symbol,Symbol)] -> a -> a
fixSubst su
  = subst (mkSubst ((expr <$>) <$> su))

instance EffectSubst Symbol Effect where
  sub su = genericSubst go fixSubst goInfo su
    where
      go (Src _ t) s = EffVar (Src s t)
      go (Eff _) s   = EffVar (Eff s)
      goInfo su (x,t)
        = withMatch su x (x, fixSubst su $ t) (\_ s' -> (s', fixSubst su t))
      -- goInfo (x,t)
      --   = withMatch su x (x,t) (\_ s' -> (s',t))

instance EffectSubst Effect EffTy where         
  sub = genericSubstTy (\s _ -> ETyVar s) go (flip const) (flip const)
    where
      go (Src _ _) e = e
      go (Eff _)   e = e

instance EffectSubst Effect Effect where         
  sub = genericSubst go (flip const) (flip const)
    where
      go (Src _ _) e = e
      go (Eff _)   e = e

instance EffectSubst EffTy EffTy where         
  sub = genericSubstTy (\x y -> y) (\s _ -> EffVar s) (flip const) (flip const)

instance EffectSubst Info EffTy where
  sub su
    = genericSubstTy (\v _ -> ETyVar v) go goInfo goCase su
    where
      goCase su x
        = withMatch su x x (\_ (Info x' _ _ _) -> x')
      goInfo su (x,t)
        = withMatch su x (x,t) (\_ (Info x' ty p _) -> (x',p))
      go b@(Eff _) _
        = EffVar b
      go b@(Src _ ty) (Info i ty' t g)
        = Pend (EffVar (Src (symbol i) (Just ty'))) (Info i ty' t g)

dom :: [(Symbol, a)] -> [Symbol]
dom = (fst <$>)

restrict :: [(Symbol, a)] -> Symbol -> [(Symbol, a)]
restrict su x
  = filter ((x /=) . fst) su

withMatch su x y f
  = case lookup (symbol x) su of
      Just e  -> f x e
      Nothing -> y

genericSubstTy f g h cf = go
  where
    go _ EffNone
      = EffNone
    go su t@(ETyVar s)
      = withMatch su s t f
    go su t@(EPi s et1 et2)
      = EPi s (go (restrict su s) et1) (go (restrict su s) et2)
    go su t@(EForAll s et)
      = EForAll s (go (restrict su s) et)
    go su t@(ETermAbs s et)
      = ETermAbs s (go (restrict su s) et)
    go su t@(EffTerm e)
      = EffTerm (genericSubst g cf h su e)

genericSubst :: (Binder -> b -> Effect)
             -> ([(Symbol, b)] -> Symbol -> Symbol)
             -> ([(Symbol, b)] -> (Symbol, SpecType) -> (Symbol, SpecType))
             -> [(Symbol, b)]
             -> Effect
             -> Effect
genericSubst f g h = goTerm
  where
    goTerm su e@(EffVar s)
      = withMatch su s e f
    goTerm su e@(EffLit _)
      = e
    goTerm su (NonDet es)
      = NonDet (goTerm su <$> es)
    goTerm su (AppEff m n)
      = AppEff (goTerm su m) (goTerm su n)
    goTerm su (AbsEff s m)
      = AbsEff s (goTerm (restrict su (symbol s)) m)
    goTerm su (Nu s m)
      = Nu s (goTerm (restrict su (symbol s)) m)
    goTerm su (Bind m f)
      = Bind (goTerm su m) (goTerm su f)
    goTerm su (Par p q)
      = Par (goTerm su p) (goTerm su q)
    goTerm su (Assume (Info x ty p env) (c, bs) e)
      = Assume (Info x' ty p' env) (c, bs) (goTerm su e)
        where (x',p') = h su (x,p)
    goTerm su (Pend e (Info x ty p env))
      = Pend (goTerm su e) (Info x' ty p' ((substf (expr . g su) <$>) <$> env))
        where (x',p') = h su (x,p)
    goTerm su (Mu s e)
      = Mu (g su s) (goTerm (restrict su (symbol s)) e)

unwrapApply :: Effect -> (Effect, [Effect])         
unwrapApply = go []
  where
    go args (AppEff m n) = go (n:args) m
    go args e            = (e, args)

occurs :: Symbol -> Effect -> Bool
occurs s e
  = s `elem` freeEffTermVars (EffTerm e)

localVars :: Effect -> [Symbol]
localVars = nub . go
  where
    go (AbsEff (Src x (Just _)) e)
      | symbolString x /= "_" = [x] ++ go e
    go (AbsEff _ e)
      = go e
    go (Nu c (Par _ e))
      = [c] ++ go e
    go (Bind e1 e2)
      = go e1 ++ go e2
    go (NonDet es)
      = concatMap go es
    go (AppEff e e')
      = go e ++ go e'
    go (Assume _ _ e)
      = go e
    go (Pend e _)
      = go e
    go (Mu _ e)
      = go e
    go _ = []

fst3 (x,_,_) = x
snd3 (_,y,_) = y
thd3 (_,_,z) = z           
