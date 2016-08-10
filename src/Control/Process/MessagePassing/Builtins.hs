module Control.Process.MessagePassing.Builtins where

import PrelNames
import Var
import Name
import Type

import Text.Printf
import Control.Process.MessagePassing.EffectTypes
import Control.Process.MessagePassing.GHCInterface

noEff :: EffTy
noEff = EffNone

recSelEff :: EffTy
recSelEff = EPi (symbol "_") noEff noEff

patErrorEff :: EffTy
patErrorEff = EPi (symbol "_") noEff (EffTerm (AbsEff (Src (symbol "_") Nothing)
                                                  (effBindF (AppEff (EffVar (Src (symbol "die") undefined))
                                                                    (EffVar me)))))


returnEffect :: [Type] -> Symbol -> EffTy
returnEffect [_,a] x
  = EPi x noEff
  $ EffTerm (AbsEff (Src x t) (effBindF (AppEff (EffVar kont) (EffVar (Src x t)))))
  -- $ EffTerm (AbsEff (Src x t) (effBindF (AppEff (AppEff (EffVar kont) (EffVar (Src x t))) (EffVar me))))
  where
    t = Just a

bindEffect :: [Type] -> Symbol -> EffTy
bindEffect [_,a,b] x
  = ETermAbs e0Sym
             $ ETermAbs e1Sym
             $ EPi actSym (EffTerm (EffVar (Eff e0Sym)))
             $ EPi fSym
                 (EPi xSym noEff
                        (EffTerm (absEff (Src actSym Nothing)
                                 (absEff (Src xSym Nothing)
                                 (AppEff (EffVar (Eff e1Sym)) (EffVar (Src xSym Nothing)))))))
                 (EffTerm (absEff (Src actSym Nothing)
                          (absEff (Src fSym Nothing)
                          (effBindF
                           -- (AppEff (AppEff (EffVar (Eff e0Sym))
                           --          (AbsEff (Src (symbol x) tya)
                           --            (AppEff (AppEff (EffVar (Eff e1Sym)) (EffVar kont))
                           --                    (EffVar me))))
                           --  (EffVar me))))))

                           -- (AppEff (AppEff (EffVar (Eff e0Sym))
                           --          ((AppEff (AppEff (EffVar (Eff e1Sym))
                           --                            (EffVar kont)))
                           --                    (EffVar me)))
                           --  (EffVar me))))))


                           (AppEff (AppEff (EffVar (Eff e0Sym))
                                    (AbsEff (Src (symbol x) tya)
                                      (AppEff (AppEff (AppEff (EffVar (Eff e1Sym))
                                                              (EffVar (Src (symbol x) Nothing)))
                                                      (EffVar kont))
                                              (EffVar me))))
                            (EffVar me))))))
  where
    tya = Just a
    tyb = Just b
    fSym = symbol "f"
    actSym = symbol "act"
    e0Sym = symbol "e0"
    e1Sym = symbol "e1"
    xSym = symbol "x"

thenEffect :: [Type] -> EffTy
thenEffect [_,a,b]
  = ETermAbs e0Sym
             $ ETermAbs e1Sym
             $ EPi fSym (EffTerm (EffVar (Eff e0Sym)))
             $ EPi gSym (EffTerm (absEff (Src fSym Nothing) (EffVar (Eff e1Sym))))
             $ EffTerm (absEff (Src fSym Nothing) (absEff (Src gSym Nothing)
                                 (effBindF (AppEff (AppEff (EffVar (Eff e0Sym))
                                              (AbsEff (Src (symbol "_") tyA)
                                                        (AppEff (AppEff (EffVar (Eff e1Sym)) (EffVar kont))
                                                                (EffVar me))))
                                            (EffVar me)))))
  where
    tyA = Just a
    tyB = Just b
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
me   = Src (symbol "me" ) Nothing

builtins      = []
classBuiltins = [("Control.Exception.Base", "patError",
              EPi (symbol "_") noEff (EffTerm (AbsEff (Src (symbol "_") Nothing)
                                                  (effBindF (AppEff (EffVar (Src (symbol "die") Nothing))
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

builtinClassEffect :: Var -> [Type] -> EffectM (Maybe EffTy)
builtinClassEffect f tys
  | getName f == bindMName
  = Just . bindEffect tys <$> freshTermVar
  | getName f == returnMName
  = Just . returnEffect tys <$> freshTermVar
  | getName f == thenMName
  = return $ Just (thenEffect tys)
  | otherwise
  = consult (getName f) classBuiltins
