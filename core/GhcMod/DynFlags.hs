{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE CPP #-}

module GhcMod.DynFlags where

import Control.Applicative
import Control.Monad
import GHC
import qualified GHC as G
import GHC.Paths (libdir)
import qualified GhcMod.Gap as Gap
import GhcMod.Types
import GhcMod.DebugLogger
import GhcMod.DynFlagsTH
import System.IO.Unsafe (unsafePerformIO)
import Prelude

-- For orphans
#if __GLASGOW_HASKELL__ == 802
import Util (OverridingBool(..))
import PprColour
#endif

setEmptyLogger :: DynFlags -> DynFlags
setEmptyLogger df =
    Gap.setLogAction df $ \_ _ _ _ _ _ -> return ()

setDebugLogger :: (String -> IO ()) -> DynFlags -> DynFlags
setDebugLogger put df = do
  Gap.setLogAction df (debugLogAction put)

-- * Fast
-- * Friendly to foreign export
-- * Not friendly to -XTemplateHaskell and -XPatternSynonyms
-- * Uses little memory
setHscNothing :: DynFlags -> DynFlags
setHscNothing df = df {
    ghcMode   = CompManager
  , ghcLink   = NoLink
  , hscTarget = HscNothing
  , optLevel  = 0
  }

-- * Slow
-- * Not friendly to foreign export
-- * Friendly to -XTemplateHaskell and -XPatternSynonyms
-- * Uses lots of memory
setHscInterpreted :: DynFlags -> DynFlags
setHscInterpreted df = df {
    ghcMode   = CompManager
  , ghcLink   = LinkInMemory
  , hscTarget = HscInterpreted
  , optLevel  = 0
  }

-- | Parse command line ghc options and add them to the 'DynFlags' passed
addCmdOpts :: GhcMonad m => Bool -> [GHCOption] -> DynFlags -> m DynFlags
addCmdOpts hideAllPackages cmdOpts df =
    if not hideAllPackages
      then fst3 <$> G.parseDynamicFlags df (map G.noLoc cmdOpts)
      else
        --
        -- Passes "-hide-all-packages" to the GHC API to prevent parsing of
        -- package environment files. However this only works if there is no
        -- invocation of `setSessionDynFlags` before calling `initDynFlagsPure`.
        -- See ghc tickets #15513, #15541.
        --    Thanks @lspitzner
        fst3 <$> G.parseDynamicFlags df (map G.noLoc ("-hide-all-packages":cmdOpts))
        -- fst3 <$> G.parseDynamicFlags df (map G.noLoc cmdOpts)
  where
    fst3 (a,_,_) = a

----------------------------------------------------------------

withDynFlags :: GhcMonad m
             => (DynFlags -> DynFlags)
             -> m a
             -> m a
withDynFlags setFlags body = G.gbracket setup teardown (\_ -> body)
  where
    setup = do
        dflags <- G.getSessionDynFlags
        void $ G.setSessionDynFlags (setFlags dflags)
        return dflags
    teardown = void . G.setSessionDynFlags

withCmdFlags :: GhcMonad m => Bool -> [GHCOption] -> m a -> m a
withCmdFlags hideAllPackages flags body = G.gbracket setup teardown (\_ -> body)
  where
    setup = do
        dflags <- G.getSessionDynFlags
        void $ G.setSessionDynFlags =<< addCmdOpts hideAllPackages flags dflags
        return dflags
    teardown = void . G.setSessionDynFlags

----------------------------------------------------------------

-- | Set 'DynFlags' equivalent to "-w:".
setNoWarningFlags :: DynFlags -> DynFlags
setNoWarningFlags df = df { warningFlags = Gap.emptyWarnFlags}

-- | Set 'DynFlags' equivalent to "-Wall".
setAllWarningFlags :: DynFlags -> DynFlags
setAllWarningFlags df = df { warningFlags = allWarningFlags }

allWarningFlags :: Gap.WarnFlags
allWarningFlags = unsafePerformIO $
    G.runGhc (Just libdir) $ do
        df <- G.getSessionDynFlags
        df' <- addCmdOpts False ["-Wall"] df
        return $ G.warningFlags df'

----------------------------------------------------------------

deferErrors :: Monad m => DynFlags -> m DynFlags
deferErrors df = return $
  Gap.setWarnTypedHoles $ Gap.setDeferTypedHoles $
  Gap.setDeferTypeErrors $ setNoWarningFlags df

----------------------------------------------------------------

#if __GLASGOW_HASKELL__ == 802
deriving instance Eq OverridingBool
deriving instance Eq PprColour.Scheme
deriving instance Eq PprColour.PprColour
#endif

deriveEqDynFlags [d|
  eqDynFlags :: DynFlags -> DynFlags -> [[(Bool, String)]]
  eqDynFlags = undefined
 |]
