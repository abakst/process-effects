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

data Assm                        

data EffTy  = EPi Symbol EffTy EffTy 
            | EForAll Symbol EffTy
            | ETyVar Symbol
            | ETermAbs Symbol EffTy
            | ETyApp EffTy EffTy
            | EffTerm Effect
            | EffNone
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
  sub su = genericSubstTy (const ETyVar) go goInfo su
    where
      go (Src _) s = EffVar (Src s)
      go (Eff _) s = EffVar (Eff s)
      goInfo (x,t)
        = withMatch su x (x, fixSubst su <$> t) (\_ s' -> (s', fixSubst su t))

fixSubst :: Subable a => [(Symbol,Symbol)] -> a -> a
fixSubst su
  = subst (mkSubst ((expr <$>) <$> su))

instance EffectSubst Symbol Effect where
  sub su = genericSubst go id su
    where
      go (Src _) s = EffVar (Src s)
      go (Eff _) s = EffVar (Eff s)
      -- goInfo (x,t)
      --   = withMatch su x (x,t) (\_ s' -> (s',t))

instance EffectSubst Effect EffTy where         
  sub = genericSubstTy (\s _ -> ETyVar s) go id
    where
      go b@(Src _) _ = EffVar b
      go (Eff _) e   = e

instance EffectSubst Effect Effect where         
  sub = genericSubst go id
    where
      go b@(Src _) _ = EffVar b
      go (Eff _) e   = e

instance EffectSubst EffTy EffTy where         
  sub = genericSubstTy (\x y -> y) (\s _ -> EffVar s) id

newtype Info = Info (Symbol, SpecType)      
instance EffectSubst Info EffTy where
  sub su
    = genericSubstTy (\v _ -> ETyVar v) go goInfo su
    where
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

genericSubstTy f g h = go
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
      = EffTerm (genericSubst g h su e)

genericSubst :: (Binder -> b -> Effect)
             -> ((Symbol, SpecType) -> (Symbol, SpecType))
             -> [(Symbol, b)]
             -> Effect
             -> Effect
genericSubst g h = goTerm
  where
    goTerm su e@(EffVar s)
      = withMatch su s e g
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
    goTerm su (Bind m g)
      = Bind (goTerm su m) (goTerm su g)
    goTerm su (Par p q)
      = Par (goTerm su p) (goTerm su q)
    goTerm su (Assume s (c, bs) e)
      = Assume s (c, bs) (goTerm su e)
    goTerm su (Pend e i)
      = Pend (goTerm su e) (h i)
