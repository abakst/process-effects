module Language.Haskell.MessagePassing.EffEnv where

import Name
import Var
import Annotations
import Serialized
import qualified Data.Map.Strict as M
import           Data.Maybe
import           Control.Monad.State

import           Language.Haskell.MessagePassing.EffectTypes
import           Language.Haskell.MessagePassing.GHCInterface
import           Language.Haskell.MessagePassing.Builtins
import           Language.Haskell.MessagePassing.Parse

 
type EffEnv = M.Map Name EffTy

  

lookupEffTy :: EffEnv -> Var -> EffectM (Maybe EffTy)
lookupEffTy g x
  | isRecordSel x
  = return $ Just recSelEff
  | getName x `M.member` g
  = return $ M.lookup (getName x) g
  | otherwise
  = do as  <- lookupAnn x
       consult as
       {- freshFnEff eff -} {- >>= dbgTy "synthEff: Var" -}
       -- liftIO $ putStrLn (show as)
  where
    consult [t] = case parseEffTy t of
                    Right et -> return $ Just et
                    _        -> return Nothing
    consult _   = return Nothing

lookupAnn :: Var -> EffectM [String]
lookupAnn v
  = do e <- gets annenv
       let tgt = NamedTarget (getName v)
       return $ findAnns deserializeWithData e tgt
