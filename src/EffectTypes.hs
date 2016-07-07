{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleInstances #-}
module EffectTypes ( Binder(..)
                   , Effect(..)
                   , EffTy(..)
                   , EffectSubst(..)
                   , Info(..)
                   , symbolString
                   , symbol
                   , dom
                   , catSubst
                   ) where

import Var
import Data.Function
import Data.List
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Types.RefType
import Language.Fixpoint.Types hiding (SrcSpan(..), ECon, filterSubst, catSubst) 
  
data Binder = Src Symbol
            | Eff Symbol
              deriving (Eq, Show)
  
data Effect = EffLit String
            | AppEff Effect Effect
            | AbsEff Binder Effect
            | EffVar Binder
            | Bind Effect Effect
            | Dummy String
            | Nu Symbol Effect
            | Par Effect Effect
            | Pend Effect (Symbol, (Id, SpecType))
              deriving Show

data EffTy  = EPi Symbol EffTy EffTy 
            | EForAll Symbol EffTy
            | ETyVar Symbol
            | ETermAbs Symbol EffTy
            | ETyApp EffTy EffTy
            | EffTerm Effect
              deriving Show

instance Symbolic Binder where
  symbol (Src x) = x
  symbol (Eff x) = x
                   
filterSubst f su
  = [ (x,y) | (x,y) <- su, f x y ]

catSubst :: [(Symbol, a)] -> [(Symbol, a)] -> [(Symbol, a)]
catSubst su1 su2
  = sub su2 su1 ++ filterSubst uniq su2
  where
    uniq k _ = k `notElem` dom su1


class EffectSubst a b where
  sub :: [(Symbol, a)] -> b -> b

instance EffectSubst a (Symbol, a) where
  sub su (s, x) =
    case lookup s su of
      Just x' -> (s, x')
      Nothing -> (s, x)

instance EffectSubst a b => EffectSubst a [b] where
  sub su = (sub su <$>)

instance EffectSubst Symbol EffTy where
  sub = genericSubstTy (\_ s -> ETyVar s) go
    where
      go (Src _) s = EffVar (Src s)
      go (Eff _) s = EffVar (Eff s)

instance EffectSubst Symbol Effect where
  sub = genericSubst go
    where
      go (Src _) s = EffVar (Src s)
      go (Eff _) s = EffVar (Eff s)

instance EffectSubst Effect EffTy where         
  sub = genericSubstTy (\s _ -> ETyVar s) go
    where
      go b@(Src _) _ = EffVar b
      go (Eff _) e   = e

instance EffectSubst Effect Effect where         
  sub = genericSubst go
    where
      go b@(Src _) _ = EffVar b
      go (Eff _) e   = e

instance EffectSubst EffTy EffTy where         
  sub = genericSubstTy (\_ e -> e) (\s _ -> EffVar s)

newtype Info = Info (Id, SpecType)      
instance EffectSubst Info EffTy where
  sub
    = genericSubstTy (\v _ -> ETyVar v) go 
    where
      go b@(Eff _) _
        = EffVar b
      go b@(Src _) (Info (i, t))
        = Pend (EffVar (Src (symbol i))) (symbol b, (i, t))

dom :: [(Symbol, a)] -> [Symbol]
dom = (fst <$>)

restrict :: [(Symbol, a)] -> Symbol -> [(Symbol, a)]
restrict su x
  = filter ((x /=) . fst) su

withMatch su x y f
  = case lookup (symbol x) su of
      Just e  -> f x e
      Nothing -> y

genericSubstTy f g = go
  where
    go su t@(ETyVar s)
      = withMatch su s t f
    go su t@(EPi s et1 et2)
      = EPi s (go (restrict su s) et1) (go (restrict su s) et2)
    go su t@(EForAll s et)
      = EForAll s (go (restrict su s) et)
    go su t@(ETermAbs s et)
      = ETermAbs s (go (restrict su s) et)
    go su t@(EffTerm e)
      = EffTerm (genericSubst g su e)

genericSubst g = goTerm
  where
    goTerm su e@(EffVar s)
      = withMatch su s e g
    goTerm su e@(EffLit _)
      = e
    goTerm su (AppEff m n)
      = AppEff (goTerm su m) (goTerm su n)
    goTerm su (AbsEff s m)
      = AbsEff s (goTerm (restrict su (symbol s)) m)
    goTerm su (Nu s m)
      = Nu s (goTerm (restrict su (symbol s)) m)
    goTerm su (Bind m g)
      = Bind (goTerm su m) (goTerm su g)
    goTerm su (Par p q)
      = Par (goTerm su p) (goTerm su q)
    goTerm su (Pend e i)
      = Pend (goTerm su e) i
