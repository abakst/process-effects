module Control.Process.MessagePassing.PostPlugin ( lhplug ) where

import Data.Map.Strict as M
import Control.Monad.Reader
import Control.Monad.State
import System.FilePath
import Text.PrettyPrint.HughesPJ hiding ((<$>))

import HscTypes hiding (lookupType)
import Annotations
import DynFlags
import StaticFlags

import Control.Process.MessagePassing.Effects
import Control.Process.MessagePassing.EffectTypes

import Language.Haskell.Liquid.Types hiding (config, target)
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Plugin as P hiding (target)
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.UX.Tidy

import Language.Fixpoint.Types hiding (PPrint(..), SrcSpan(..), ECon) 
import Language.Fixpoint.Utils.Files (tempDirectory)
import qualified Language.Fixpoint.Types as Fp

lhplug :: Plugin
lhplug = PostPlugin { P.name   = "Message Passing Effects"
                    , P.plugin = DoPostStep doEffects
                    }

doEffects :: AnnInfo SpecType -> ReaderT PluginEnv IO ()
doEffects (AI m)
  = do core <- reader P.cbs
       hsenv <- env <$> reader ghcInfo
       info  <- reader ghcInfo
       let sp  = spec info
       mod   <- targetMod <$> reader ghcInfo
       emb <- reader embed
       f:_  <- files <$> reader config
       let annmap = (snd <$>) <$> m
           tmpdir = tempDirectory f
       liftIO $ do
         initStaticOpts
         setUnsafeGlobalDynFlags (extractDynFlags hsenv)
         annenv <- prepareAnnotations hsenv Nothing
         let assm0 = (val <$>) <$> asmSigs sp
             assm1 = [ (x,val t) | (x,t) <- tySigs sp, x `elem` impVars info ]
         oblig  <- 
           evalStateT (synthEffects M.empty core) EffState { ctr = 0
                                                           , annots = annmap
                                                           , annenv = annenv
                                                           , tyconEmb = emb
                                                           , target = mod
                                                           , esubst = []
                                                           , tsubst = []
                                                           , hsenv = hsenv
                                                           , assms = assm0 ++ assm1
                                                           }
         case oblig of
           Just o  -> write tmpdir o
           Nothing -> return ()
  where
    write f o = writeFile (f </> "out.pml") (render o)
