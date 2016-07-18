module Control.Process.MessagePassing.EffEnv where

import Name
import Var
import Annotations
import Serialized
import qualified Data.Map.Strict as M
import           Data.Maybe
import           Control.Monad.State

import           Control.Process.MessagePassing.EffectTypes
import           Control.Process.MessagePassing.GHCInterface
import           Control.Process.MessagePassing.Builtins
import           Control.Process.MessagePassing.Parse

 
type EffEnv = M.Map Name EffTy

lookupString :: EffEnv -> String -> Maybe EffTy
lookupString g s
  = case [ v | (k,v) <- M.toList g, eq k ] of
      v:_ -> Just v
      _   -> Nothing
    where
      eq x = getOccString x == s

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
