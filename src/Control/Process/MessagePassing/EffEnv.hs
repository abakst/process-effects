module Control.Process.MessagePassing.EffEnv where

import Name
import Var
import Type
import Annotations
import Serialized
import qualified Data.Map.Strict as M
import           Data.Maybe
import           Control.Monad.State

import           Control.Process.MessagePassing.EffectTypes
import           Control.Process.MessagePassing.GHCInterface
import           Control.Process.MessagePassing.Builtins
import           Control.Process.MessagePassing.Parse

 
type EffEnv r = M.Map Var (EffTy, Maybe r)

lookupString :: EffEnv r -> String -> Maybe EffTy
lookupString g s
  = case [ v | (k,v) <- M.toList g, eq k ] of
      (e,_):_ -> Just e
      _   -> Nothing
    where
      eq x = getOccString x == s
      -- eq x = symbolString x == s

lookupEffTy :: EffEnv r -> Var -> EffectM (Maybe EffTy)
lookupEffTy g x
  = (fst <$>) <$> lookupEffTyEnv g x

lookupReft :: EffEnv r -> Var -> EffectM (Maybe r)
lookupReft g x
  = join . (snd <$>) <$> lookupEffTyEnv g x

extend :: EffEnv r -> Var -> EffTy -> Maybe r -> EffEnv r
extend g x t p = M.insert x (t,p) g

bindings = M.elems

lookupEffTyEnv :: EffEnv r -> Var -> EffectM (Maybe (EffTy, Maybe r))
lookupEffTyEnv g x
  | isRecordSel x
  = return $ Just (recSelEff, Nothing)
  | x `M.member` g
  = return $ M.lookup x g
  | otherwise
  = do as  <- lookupAnn x
       consult as
  where
    consult [t] = case parseEffTy t of
                    Right et -> return $ Just (et, Nothing)
                    _        -> return Nothing
    consult _   = return Nothing

lookupAnn :: Var -> EffectM [String]
lookupAnn v
  = do e <- gets annenv
       let tgt = NamedTarget (getName v)
       return $ findAnns deserializeWithData e tgt
