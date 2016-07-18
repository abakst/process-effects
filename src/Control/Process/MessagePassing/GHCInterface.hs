module Control.Process.MessagePassing.GHCInterface where

import GHC
import Var
import Id  
import OccName
import Name
import IfaceEnv
import IdInfo
import TcRnMonad
import Finder
import HscTypes
import Control.Monad.IO.Class


-- Looking up names
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

-- Distinguishing types & special expressions                    
isRecordSel :: Var -> Bool
isRecordSel x
  = case idDetails x of
      RecSelId {} -> True
      _           -> False
