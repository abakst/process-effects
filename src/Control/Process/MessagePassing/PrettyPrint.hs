module Control.Process.MessagePassing.PrettyPrint where

import           DataCon
import           Control.Process.MessagePassing.EffectTypes
import           Text.PrettyPrint.HughesPJ hiding ((<$>))
import qualified Language.Fixpoint.Types as Fp
import qualified Language.Haskell.Liquid.Types as Rt

class Pretty a where
  pprintPrec :: Int -> a -> Doc

parensIf True  = parens
parensIf False = id

lambda x e =
  text "λ" <> x <> text "." <> e

pretty :: Pretty a => a -> Doc
pretty = pprintPrec 0

instance Pretty a => Pretty [a] where
  pprintPrec z l
    =  hsep . punctuate comma $ fmap (pprintPrec z) l
         
instance Pretty Binder where
  pprintPrec z (Src b (Just t)) = pprintPrec z (symbol b) <> colon
  pprintPrec z (Src b _)        = text "?" <> pprintPrec z (symbol b)
  pprintPrec z (Eff b)          = text "^" <> pprintPrec z (symbol b) <> text "^"

instance Pretty Fp.Symbol where
  pprintPrec _ s = text (symbolString s)

maybeAnnot :: Info -> Doc -> Doc                   
maybeAnnot i@(Info (x,_,Fp.RR so (Fp.Reft (vv,p)))) d
  = if not $ Fp.isTautoPred p then
      d <+> parens (text "where" <+> 
                         Fp.pprint (Fp.subst1 p (vv, Fp.expr (symbol x))))
     else
       d

instance Pretty Info where
  pprintPrec _ (Info (x,_,reft))
    = Fp.pprint (x, reft)

instance Pretty Effect where
  pprintPrec z (EffLit s)
    = text s
  pprintPrec z (EffVar v)
    = text (symbolString (symbol v))
  pprintPrec z (Pend e i)
    = maybeAnnot i (pprintPrec z e)
  pprintPrec z (NonDet es)
    = parensIf (z > za) $
      hcat (punctuate (text " □ ") (pprintPrec (za+1) <$> es))
    where
      za = 2
  pprintPrec z (Assume i@(Info (s,_,_)) (c,bs) e)
    = parensIf (z > za) $
      text "case" <+> maybeAnnot i (pprintPrec 0 s) <+> text "of" <+>
           parens (pprintPrec 0 (symbol (dataConName c)) <+> hsep (pprintPrec 0 <$> bs)) <+> text "->"
      <+> pprintPrec (za+1) e 
    where
      za = 2
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
  pprintPrec z (Mu b e)
    = parensIf (z > za) $
      text "μ" <> pprintPrec z b <> text "." <+> pprintPrec (za + 1) e
    where
      za = 3
  pprintPrec z (Bind e1 e2)
    = parensIf (z > za)
        (pprintPrec (za + 1) e1 <+>
         text ">>=" <+>
         pprintPrec (za + 1) e2)
    where
      za = 2
  pprintPrec z (Par e1 e2)
    = parensIf (z > za) $
        (pprintPrec (za + 1) e1 <+>
         text "|" <+>
         pprintPrec (za + 1) e2)
    where
      za = 6
