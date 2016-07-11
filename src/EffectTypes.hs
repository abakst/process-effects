{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleInstances #-}
module EffectTypes ( Binder(..)
                   , Effect(..)
                   , EffTy(..)
                   , EffectSubst(..)
                   , Info(..)
                   , freeEffTyVars
                   , freeEffTermVars
                   , symbolString
                   , symbol
                   , dom
                   , catSubst
                   ) where

import Debug.Trace

import Var
import Data.Function
import Data.List
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Types.RefType
import Language.Fixpoint.Types hiding (SrcSpan(..), ECon, filterSubst, catSubst) 
  
debug s x = trace (s ++ ": " ++ show x) x  
data Binder = Src Symbol
            | Eff Symbol
              deriving (Eq, Show)
  
data Effect = EffLit String
            | AppEff Effect Effect
            | AbsEff Binder Effect
            | EffVar Binder
            | Bind Effect Effect
            | NonDet [Effect]
            | Nu Symbol Effect
            | Par Effect Effect
            | Assume Symbol (Symbol, [Symbol]) Effect
            | Pend Effect (Symbol, SpecType)
              deriving Show

data EffTy  = EPi Symbol EffTy EffTy 
            | EForAll Symbol EffTy
            | ETyVar Symbol
            | ETermAbs Symbol EffTy
            | ETyApp EffTy EffTy
            | EffTerm Effect
            | EffNone
              deriving Show

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
    go (AbsEff (Src _) e2) = go e2
    go (AbsEff (Eff x) e2) = go e2 \\ [x]
    go (Bind e1 e2)        = collect go e1 e2
    go (NonDet es)         = nub (concatMap go es)
    go (Nu s e)            = go e
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
  symbol (Src x) = x
  symbol (Eff x) = x
                   
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
  sub su = genericSubstTy (const ETyVar) go goInfo (fixSubst su) su
    where
      go (Src _) s = EffVar (Src s)
      go (Eff _) s = EffVar (Eff s)
      goInfo (x,t)
        = withMatch su x (x, fixSubst su <$> t) (\_ s' -> (s', fixSubst su t))

fixSubst :: Subable a => [(Symbol,Symbol)] -> a -> a
fixSubst su
  = subst (mkSubst ((expr <$>) <$> su))

instance EffectSubst Symbol Effect where
  sub su = genericSubst go (fixSubst su) goInfo su
    where
      go (Src _) s = EffVar (Src s)
      go (Eff _) s = EffVar (Eff s)
      goInfo (x,t)
        = withMatch su x (x, fixSubst su <$> t) (\_ s' -> (s', fixSubst su t))
      -- goInfo (x,t)
      --   = withMatch su x (x,t) (\_ s' -> (s',t))

instance EffectSubst Effect EffTy where         
  sub = genericSubstTy (\s _ -> ETyVar s) go id id
    where
      go b@(Src _) _ = EffVar b
      go (Eff _) e   = e

instance EffectSubst Effect Effect where         
  sub = genericSubst go id id
    where
      go b@(Src _) _ = EffVar b
      go (Eff _) e   = e

instance EffectSubst EffTy EffTy where         
  sub = genericSubstTy (\x y -> y) (\s _ -> EffVar s) id id

newtype Info = Info (Symbol, SpecType)      
instance EffectSubst Info EffTy where
  sub su
    = genericSubstTy (\v _ -> ETyVar v) go goInfo goCase su
    where
      goCase x
        = withMatch su x x (\_ (Info (x',_)) -> x')
      goInfo (x,t)
        = withMatch su x (x,t) (\_ (Info (x',t')) -> (x',t))
      go b@(Eff _) _
        = EffVar b
      go b@(Src _) (Info (i, t))
        = Pend (EffVar (Src (symbol i))) (i, t)

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
             -> (Symbol -> Symbol)
             -> ((Symbol, SpecType) -> (Symbol, SpecType))
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
    goTerm su (Assume s (c, bs) e)
      = Assume (g s) (c, bs) (goTerm su e)
    goTerm su (Pend e i)
      = Pend (goTerm su e) (h i)
