module Control.Process.MessagePassing.PostPlugin ( lhplug ) where

import Data.Map.Strict as M
import Control.Monad.Reader
import Control.Monad.State

import HscTypes hiding (lookupType)
import Annotations
import DynFlags

import Control.Process.MessagePassing.Effects
import Control.Process.MessagePassing.EffectTypes

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Plugin as P
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.UX.Tidy

import Language.Fixpoint.Types hiding (PPrint(..), SrcSpan(..), ECon) 
import qualified Language.Fixpoint.Types as Fp

lhplug :: Plugin
lhplug = PostPlugin { P.name   = "Message Passing Effects"
                    , P.plugin = DoPostStep doEffects
                    }

doEffects :: AnnInfo SpecType -> ReaderT PluginEnv IO ()
doEffects (AI m)
  = do core <- reader P.cbs
       hsenv <- env <$> reader ghcInfo
       emb <- reader embed
       let annmap = (rTypeSortedReft emb . snd <$>) <$> m
       liftIO $ do
         setUnsafeGlobalDynFlags (extractDynFlags hsenv)
         annenv <- prepareAnnotations hsenv Nothing
         evalStateT (synthEffects M.empty core) EffState { ctr = 0
                                                         , annots = annmap
                                                         , annenv = annenv
                                                         , tyconEmb = emb
                                                         , esubst = []
                                                         , tsubst = []
                                                         , hsenv = hsenv
                                                         }
