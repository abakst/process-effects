module Language.Haskell.MessagePassing.Builtins where

import PrelNames
import Var
import Name

import Text.Printf
import Language.Haskell.MessagePassing.EffectTypes
import Language.Haskell.MessagePassing.GHCInterface

noEff :: EffTy
noEff = EffNone

recSelEff :: EffTy
recSelEff = EPi (symbol "_") noEff noEff

patErrorEff :: EffTy
patErrorEff = EPi (symbol "_") noEff (EffTerm (AbsEff (Src (symbol "_"))
                                                  (effBindF (AppEff (EffVar (Src (symbol "die")))
                                                                    (EffVar me)))))


returnEffect :: Symbol -> EffTy
returnEffect x
  = EPi x noEff
  $ EffTerm (AbsEff (Src x) (effBindF (AppEff (AppEff (EffVar kont) (EffVar (Src x))) (EffVar me))))

bindEffect :: Symbol -> EffTy
bindEffect x
  = ETermAbs e0Sym
             $ ETermAbs e1Sym
             $ EPi actSym (EffTerm (EffVar (Eff e0Sym)))
             $ EPi fSym
                 (EPi xSym noEff
                        (EffTerm (EffVar (Eff e1Sym))))
                 (EffTerm (absEff (Src actSym)
                          (absEff (Src fSym)
                          (effBindF
                           (AppEff (AppEff (EffVar (Eff e0Sym))
                                    (AbsEff (Src (symbol x))
                                      (AppEff (AppEff (AppEff (EffVar (Eff e1Sym))
                                                              (EffVar (Src (symbol x))))
                                                      (EffVar kont))
                                              (EffVar me))))
                            (EffVar me))))))
  where
    fSym = symbol "f"
    actSym = symbol "act"
    e0Sym = symbol "e0"
    e1Sym = symbol "e1"
    xSym = symbol "x"

thenEffect :: EffTy
thenEffect = ETermAbs e0Sym
             $ ETermAbs e1Sym
             $ EPi fSym (EffTerm (EffVar (Eff e0Sym)))
             $ EPi gSym (EffTerm (EffVar (Eff e1Sym)))
             $ EffTerm (absEff (Src fSym) (absEff (Src gSym)
                                 (effBindF (AppEff (AppEff (EffVar (Eff e0Sym))
                                              (AbsEff (Src (symbol "_"))
                                                        (AppEff (AppEff (EffVar (Eff e1Sym)) (EffVar kont))
                                                                (EffVar me))))
                                            (EffVar me)))))
  where
    fSym = symbol "f"
    gSym = symbol "g"
    e0Sym = symbol "e0"
    e1Sym = symbol "e1"

effBindF :: Effect -> Effect
effBindF = callCC . withPid

callCC :: Effect -> Effect
callCC = absEff kont

withCC :: EffTy -> EffTy
withCC = ETermAbs (symbol "K")

withPid :: Effect -> Effect
withPid = absEff me

absEff :: Binder -> Effect -> Effect
absEff x e = AbsEff x e

me, kont :: Binder
kont = Eff (symbol "$K")
me   = Src (symbol "me")

builtins      = []
classBuiltins = [("Control.Exception.Base", "patError",
              EPi (symbol "_") noEff (EffTerm (AbsEff (Src (symbol "_"))
                                                  (effBindF (AppEff (EffVar (Src (symbol "die")))
                                                                    (EffVar me))))))
           ]

builtinEffect :: Var -> EffectM (Maybe EffTy)
builtinEffect x
  = consult (getName x) builtins -- sigh

consult :: Name -> [(String, String, EffTy)] -> EffectM (Maybe EffTy)
consult x ((m,n,t):ns)
  = do env  <- gets hsenv
       f    <- ghcVarName env m n
       if x == f then
         return (Just t)
       else
         consult x ns
consult _ []
  = return Nothing

builtinClassEffect :: Var -> EffectM (Maybe EffTy)
builtinClassEffect f
  | getName f == bindMName
  = Just . bindEffect   <$> freshTermVar
  | getName f == returnMName
  = Just . returnEffect <$> freshTermVar
  | getName f == thenMName
  = return $ Just thenEffect
  | otherwise
  = consult (getName f) classBuiltins
