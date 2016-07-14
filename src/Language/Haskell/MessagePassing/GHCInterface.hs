module GHCInterface where

import GHC
import OccName
import Name
import IfaceEnv
import TcRnMonad
import Finder
import HscTypes
import Control.Monad.IO.Class

ghcVarName :: MonadIO m => HscEnv -> String -> String -> m Name  
ghcVarName env mod var
  = do let occNm = mkOccName OccName.varName var 
       m  <- liftIO $ lookupMod env (mkModuleName mod) 
       liftIO $ initTcForLookup env (lookupOrig m occNm)

lookupMod :: HscEnv -> ModuleName -> IO Module
lookupMod hsc_env mod_nm = do
    found_module <- findImportedModule hsc_env mod_nm Nothing
    case found_module of
      Found _ md -> return md
      _          -> error $ "Unable to resolve module looked up by plugin: " ++ moduleNameString mod_nm --      return t
