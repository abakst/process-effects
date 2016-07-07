module PrettyPrint where

import           EffectTypes
import           Text.PrettyPrint.HughesPJ
import           Language.Fixpoint.Types hiding (PPrint(..))

class Pretty a where
  pprintPrec :: Int -> a -> Doc

parensIf True  = parens
parensIf False = id

lambda x e =
  text "λ" <> x <> text "." <> e

pretty :: Pretty a => a -> Doc
pretty = pprintPrec 0       

instance Pretty Binder where
  pprintPrec z b = pprintPrec z (symbol b)

instance Pretty Symbol where
  pprintPrec _ s = text (symbolString s)

instance Pretty Effect where
  pprintPrec z (EffLit s)
    = text s
  pprintPrec z (EffVar v)
    = text (symbolString (symbol v))
  pprintPrec z (Pend e _)
    = pprintPrec z e
  pprintPrec z (Dummy s)
    = text s
  pprintPrec z (AppEff e1 e2)
    = parensIf (z > za) $
      pprintPrec za e1 <+> pprintPrec (za+1) e2
    where
      za = 4
  pprintPrec z (AbsEff b e)
    = parensIf (z > za) $
      lambda (pprintPrec z b) (pprintPrec za e)
    where
      za = 3
  pprintPrec z (Nu b e)
    = parensIf (z > za) $
      parens (text "ν" <+> pprintPrec z b) <> pprintPrec (za + 1) e
    where
      za = 7
  pprintPrec z (Bind e1 e2)
    = parensIf (z > za)
        (pprintPrec (za + 1) e1 <+>
         text ">>=" <+>
         pprintPrec (za + 1) e2)
    where
      za = 5
  pprintPrec z (Par e1 e2)
    = parensIf (z > za) $
        (pprintPrec (za + 1) e1 <+>
         text "|" <+>
         pprintPrec (za + 1) e2)
    where
      za = 6
