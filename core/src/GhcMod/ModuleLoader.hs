{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Uses GHC hooks to load a TypecheckedModule

module GhcMod.ModuleLoader
  ( getTypecheckedModuleGhc
  , getTypecheckedModuleGhc'
  , HasGhcModuleCache(..)
  , GhcModuleCache(..)
  , CachedModule(..)
  , UriCache(..)
  , LocMap
  , Pos(..)
  , modifyCache
  , emptyModuleCache
  , ModuleCache(..)
  -- * foo
  , cachedModules
  , getCachedModule
  , withCachedModule
  , withCachedModuleAndData
  , cacheModule
  , deleteCachedModule
  , getCradle
  , runActionWithContext
  , genLocMap
  -- , getNamesAtPos
  , unpackRealSrcSpan
  , toPos
  , genTypeMap
  , getArtifactsAtPos
  , unpackRealSrcSpan
  , toPos
  ) where

import           Control.Monad.State.Strict hiding (put,get,modify,gets)
import           Data.Char
import qualified Data.Generics                     as SYB
import Data.Generics (Proxy(..), TypeRep, typeRep, typeOf) 
import           Data.Dynamic
import qualified Data.IntervalMap.FingerTree       as IM
import qualified Data.Map                          as Map
import           Data.Maybe
import qualified Data.Text                         as T
import           GHC                               (TypecheckedModule)
import qualified GhcMod.Cradle                     as GM
import qualified GhcMod.Monad                      as GM
import qualified GhcMod.Target                     as GM
import qualified GhcMod.Types                      as GM
import           System.Directory
import           System.FilePath

import qualified DynFlags                          as GHC
import qualified GHC
import qualified GhcMonad                          as GHC
import qualified Hooks                             as GHC
import qualified HscMain                           as GHC
import qualified HscTypes                          as GHC
import qualified SrcLoc                            as GHC
import qualified TcRnMonad                         as GHC
import qualified Var

import Control.Monad.Trans.Control
import Exception (ExceptionMonad )

import           Data.IORef

import GhcMod.SrcUtils

-- ---------------------------------------------------------------------

getMappedFileName :: FilePath -> GM.FileMappingMap -> FilePath
getMappedFileName fname mfs =
  case Map.lookup fname mfs of
    Just fm -> GM.fmPath fm
    Nothing -> fname

canonicalizeModSummary :: (MonadIO m) =>
  GHC.ModSummary -> m (Maybe FilePath)
canonicalizeModSummary =
  traverse (liftIO . canonicalizePath) . GHC.ml_hs_file . GHC.ms_location

tweakModSummaryDynFlags :: GHC.ModSummary -> GHC.ModSummary
tweakModSummaryDynFlags ms =
  let df = GHC.ms_hspp_opts ms
  in ms { GHC.ms_hspp_opts = GHC.gopt_set df GHC.Opt_KeepRawTokenStream }

-- | Gets a TypecheckedModule from a given file
-- The `wrapper` allows arbitary data to be captured during
-- the compilation process, like errors and warnings
-- Appends the parent directories of all the mapped files
-- to the includePaths for CPP purposes.
-- Use in combination with `runActionInContext` for best results
getTypecheckedModuleGhc' :: GM.IOish m
  => (GM.GmlT m () -> GM.GmlT m a) -> FilePath -> GM.GhcModT m (a, Maybe TypecheckedModule)
getTypecheckedModuleGhc' wrapper targetFile = do
  cfileName <- liftIO $ canonicalizePath targetFile
  mfs <- GM.getMMappedFiles
  mFileName <- liftIO . canonicalizePath $ getMappedFileName cfileName mfs
  ref <- liftIO $ newIORef Nothing
  let keepInfo = pure . (mFileName ==)
      saveModule = writeIORef ref . Just
  res <- getTypecheckedModuleGhc wrapper [cfileName] keepInfo saveModule
  mtm <- liftIO $ readIORef ref
  return (res, mtm)

-- | like getTypecheckedModuleGhc' but allows you to keep an arbitary number of Modules
-- `keepInfo` decides which TypecheckedModule to keep
-- `saveModule` is the callback that is passed the TypecheckedModule
getTypecheckedModuleGhc :: GM.IOish m
  => (GM.GmlT m () -> GM.GmlT m a) -> [FilePath] -> (FilePath -> IO Bool) -> (TypecheckedModule -> IO ()) -> GM.GhcModT m a
getTypecheckedModuleGhc wrapper targetFiles keepInfo saveModule = do
  mfs <- GM.getMMappedFiles
  let ips = map takeDirectory $ Map.keys mfs
      setIncludePaths df = df { GHC.includePaths = ips ++ GHC.includePaths df }
  GM.runGmlTWith' (map Left targetFiles)
                  (return . setIncludePaths)
                  (Just $ updateHooks keepInfo saveModule)
                  wrapper
                  (return ())

updateHooks
  :: (FilePath -> IO Bool)
  -> (TypecheckedModule -> IO ())
  -> GHC.Hooks
  -> GHC.Hooks
updateHooks fp ref hooks = hooks {
#if __GLASGOW_HASKELL__ <= 710
        GHC.hscFrontendHook   = Just $ hscFrontend fp ref
#else
        GHC.hscFrontendHook   = Just $ fmap GHC.FrontendTypecheck . hscFrontend fp ref
#endif
      }


-- | Warning: discards all changes to Session
runGhcInHsc :: GHC.Ghc a -> GHC.Hsc a
runGhcInHsc action = do
  env <- GHC.getHscEnv
  session <- liftIO $ newIORef env
  liftIO $ GHC.reflectGhc action $ GHC.Session session


-- | Frontend hook that keeps the TypecheckedModule for its first argument
-- and stores it in the IORef passed to it
hscFrontend :: (FilePath -> IO Bool) -> (TypecheckedModule -> IO ()) -> GHC.ModSummary -> GHC.Hsc GHC.TcGblEnv
hscFrontend keepInfoFunc saveModule mod_summary = do
    mfn <- canonicalizeModSummary mod_summary
      -- md = GHC.moduleNameString $ GHC.moduleName $ GHC.ms_mod mod_summary
    keepInfo <- case mfn of
      Just fileName -> liftIO $ keepInfoFunc fileName
      Nothing       -> pure False
    -- liftIO $ debugm $ "hscFrontend: got mod,file" ++ show (md, mfn)
    if keepInfo
      then runGhcInHsc $ do
        let modSumWithRaw = tweakModSummaryDynFlags mod_summary

        p' <- GHC.parseModule modSumWithRaw
        let p = p' {GHC.pm_mod_summary = mod_summary}
        tc <- GHC.typecheckModule p
        let tc_gbl_env = fst $ GHC.tm_internals_ tc

        liftIO $ saveModule tc
        return tc_gbl_env
      else do
        hpm <- GHC.hscParse' mod_summary
        hsc_env <- GHC.getHscEnv
        GHC.tcRnModule' hsc_env mod_summary False hpm

-- ---------------------------------------------------------------------

type UriCaches = Map.Map FilePath UriCache

data UriCache = UriCache
  { cachedModule :: !CachedModule
  , cachedData   :: !(Map.Map TypeRep Dynamic)
  } deriving Show

data Pos = Pos { line :: Int, col :: Int}
  deriving (Eq,Show,Read,Ord)

type SourceMap a = IM.IntervalMap Pos a
type LocMap = SourceMap GHC.Name
type TypeMap = SourceMap GHC.Type

data CachedModule = CachedModule
  { tcMod          :: !TypecheckedModule
  , locMap         :: !LocMap
  , typeMap        :: !TypeMap
  , revMap         :: !(FilePath -> FilePath)
  , newPosToOldPos :: !(Pos -> Maybe Pos)
  , oldPosToNewPos :: !(Pos -> Maybe Pos)
  }

instance Show CachedModule where
  show CachedModule{} = "CachedModule { .. }"

-- ---------------------------------------------------------------------

modifyCache :: (HasGhcModuleCache m) => (GhcModuleCache -> GhcModuleCache) -> m ()
modifyCache f = do
  mc <- getModuleCache
  setModuleCache (f mc)

-- ---------------------------------------------------------------------
-- The following to move into ghc-mod-core

class (Monad m) => HasGhcModuleCache m where
  getModuleCache :: m GhcModuleCache
  setModuleCache :: GhcModuleCache -> m ()

emptyModuleCache :: GhcModuleCache
emptyModuleCache = GhcModuleCache Map.empty Map.empty

data GhcModuleCache = GhcModuleCache
  { cradleCache :: !(Map.Map FilePath GM.Cradle)
              -- ^ map from dirs to cradles
  , uriCaches  :: !UriCaches
  } deriving (Show)

-- ---------------------------------------------------------------------
-- | Runs an IdeM action with the given Cradle
withCradle :: (GM.GmEnv m) => GM.Cradle -> m a -> m a
withCradle crdl =
  GM.gmeLocal (\env -> env {GM.gmCradle = crdl})

-- ---------------------------------------------------------------------
-- | Runs an action in a ghc-mod Cradle found from the
-- directory of the given file. If no file is found
-- then runs the action in the default cradle.
-- Sets the current directory to the cradle root dir
-- in either case
runActionWithContext :: (Monad m, GM.GmEnv m, GM.MonadIO m, HasGhcModuleCache m
                        , GM.GmLog m, MonadBaseControl IO m, ExceptionMonad m, GM.GmOut m)
                     => Maybe FilePath -> m a -> m a
runActionWithContext Nothing action = do
  crdl <- GM.cradle
  liftIO $ setCurrentDirectory $ GM.cradleRootDir crdl
  action
runActionWithContext (Just uri) action = do
  crdl <- getCradle uri
  liftIO $ setCurrentDirectory $ GM.cradleRootDir crdl
  withCradle crdl action

-- | Returns all the cached modules in the IdeState
cachedModules :: GhcModuleCache -> Map.Map FilePath CachedModule
cachedModules = fmap cachedModule . uriCaches

-- | Get the Cradle that should be used for a given URI
getCradle :: (GM.GmEnv m, GM.MonadIO m, HasGhcModuleCache m, GM.GmLog m
             , MonadBaseControl IO m, ExceptionMonad m, GM.GmOut m)
          => FilePath -> m GM.Cradle
getCradle fp = do
      dir <- liftIO $ takeDirectory <$> canonicalizePath fp
      mcache <- getModuleCache
      let mcradle = (Map.lookup dir . cradleCache) mcache
      case mcradle of
        Just crdl ->
          return crdl
        Nothing -> do
          opts <- GM.options
          crdl <- GM.findCradle' (GM.optPrograms opts) dir
          -- debugm $ "cradle cache miss for " ++ dir ++ ", generating cradle " ++ show crdl
          modifyCache (\s -> s { cradleCache = Map.insert dir crdl (cradleCache s)})
          return crdl


-- | looks up a CachedModule for a given URI
getCachedModule :: (Monad m, GM.MonadIO m, HasGhcModuleCache m)
                => FilePath -> m (Maybe CachedModule)
getCachedModule uri = do
  uri' <- liftIO $ canonicalizePath uri
  mc <- getModuleCache
  return $ (Map.lookup uri' . cachedModules) mc

-- | Version of `withCachedModuleAndData` that doesn't provide
-- any extra cached data
withCachedModule :: (Monad m, GM.MonadIO m, HasGhcModuleCache m)
                 => FilePath -> m b -> (CachedModule -> m b) -> m b
withCachedModule uri noCache callback = do
  mcm <- getCachedModule uri
  case mcm of
    Nothing -> noCache
    Just cm -> callback cm

-- | Calls its argument with the CachedModule for a given URI
-- along with any data that might be stored in the ModuleCache.
-- The data is associated with the CachedModule and its cache is
-- invalidated when a new CachedModule is loaded.
-- If the data doesn't exist in the cache, new data is generated
-- using by calling the `cacheDataProducer` function
withCachedModuleAndData :: forall a b m.
  (ModuleCache a, Monad m, GM.MonadIO m, HasGhcModuleCache m)
  => FilePath -> m b -> (CachedModule -> a -> m b) -> m b
withCachedModuleAndData uri noCache callback = do
  uri' <- liftIO $ canonicalizePath uri
  mcache <- getModuleCache
  let mc = (Map.lookup uri' . uriCaches) mcache
  case mc of
    Nothing -> noCache
    Just UriCache{cachedModule = cm, cachedData = dat} -> do
      let proxy :: Proxy a
          proxy = Proxy
      a <- case Map.lookup (typeRep proxy) dat of
             Nothing -> do
               val <- cacheDataProducer cm
               let dat' = Map.insert (typeOf val) (toDyn val) dat
               modifyCache (\s -> s {uriCaches = Map.insert uri' (UriCache cm dat')
                                                                 (uriCaches s)})
               return val
             Just x ->
               case fromDynamic x of
                 Just val -> return val
                 Nothing  -> error "impossible"
      callback cm a

-- | Saves a module to the cache
cacheModule :: (Monad m, GM.MonadIO m, HasGhcModuleCache m)
            => FilePath -> CachedModule -> m ()
cacheModule uri cm = do
  uri' <- liftIO $ canonicalizePath uri
  modifyCache (\s -> s { uriCaches = Map.insert uri' (UriCache cm Map.empty)
                                                     (uriCaches s) })

-- | Deletes a module from the cache
deleteCachedModule :: (Monad m, GM.MonadIO m, HasGhcModuleCache m) => FilePath -> m ()
deleteCachedModule uri = do
  uri' <- liftIO $ canonicalizePath uri
  modifyCache (\s -> s { uriCaches = Map.delete uri' (uriCaches s) })

-- ---------------------------------------------------------------------

genTypeMap :: GHC.GhcMonad m => TypecheckedModule -> m TypeMap
genTypeMap tm = do
    ts <- collectAllSpansTypes True tm
    return $ foldr go IM.empty ts
  where
    go (GHC.RealSrcSpan spn, typ) im =
      IM.insert (uncurry IM.Interval $ unpackRealSrcSpan spn) typ im
    go _ im = im

-- | Generates a LocMap from a TypecheckedModule,
-- which allows fast queries for all the symbols
-- located at a particular point in the source
genLocMap :: TypecheckedModule -> LocMap
genLocMap tm = names
  where
    typechecked = GHC.tm_typechecked_source tm
    renamed = fromJust $ GHC.tm_renamed_source tm

    rspToInt = uncurry IM.Interval . unpackRealSrcSpan

#if __GLASGOW_HASKELL__ > 710
    names  = IM.union names2 $ SYB.everything IM.union (IM.empty `SYB.mkQ` hsRecFieldT) typechecked
#else
    names = names2
#endif
    names2 = SYB.everything IM.union (IM.empty
#if __GLASGOW_HASKELL__ > 710
                                               `SYB.mkQ`  fieldOcc
                                               `SYB.extQ` hsRecFieldN
                                               `SYB.extQ` checker) renamed
#else
                                               `SYB.mkQ` checker) renamed
#endif

    checker (GHC.L (GHC.RealSrcSpan r) x) = IM.singleton (rspToInt r) x
    checker _                             = IM.empty

#if __GLASGOW_HASKELL__ > 710
    fieldOcc :: GHC.FieldOcc GHC.Name -> LocMap
    fieldOcc (GHC.FieldOcc (GHC.L (GHC.RealSrcSpan r) _) n) = IM.singleton (rspToInt r) n
    fieldOcc _ = IM.empty

    hsRecFieldN :: GHC.LHsExpr GHC.Name -> LocMap
    hsRecFieldN (GHC.L _ (GHC.HsRecFld (GHC.Unambiguous (GHC.L (GHC.RealSrcSpan r) _) n) )) = IM.singleton (rspToInt r) n
    hsRecFieldN _ = IM.empty

    hsRecFieldT :: GHC.LHsExpr GHC.Id -> LocMap
    hsRecFieldT (GHC.L _ (GHC.HsRecFld (GHC.Ambiguous (GHC.L (GHC.RealSrcSpan r) _) n) )) = IM.singleton (rspToInt r) (Var.varName n)
    hsRecFieldT _ = IM.empty
#endif

-- -- | Seaches for all the symbols at a point in the
-- -- given LocMap
-- getNamesAtPos :: Pos -> LocMap -> [((Pos,Pos), GHC.Name)]
-- getNamesAtPos p im = map f $ IM.search p im

getArtifactsAtPos :: Pos -> SourceMap a -> [((Pos,Pos), a)]
getArtifactsAtPos p im = map f $ IM.search p im
  where f (IM.Interval a b, x) = ((a, b), x)

-- ---------------------------------------------------------------------

unpackRealSrcSpan :: GHC.RealSrcSpan -> (Pos, Pos)
unpackRealSrcSpan rspan =
  (toPos (l1,c1),toPos (l2,c2))
  where s  = GHC.realSrcSpanStart rspan
        l1 = GHC.srcLocLine s
        c1 = GHC.srcLocCol s
        e  = GHC.realSrcSpanEnd rspan
        l2 = GHC.srcLocLine e
        c2 = GHC.srcLocCol e

toPos :: (Int,Int) -> Pos
toPos (l,c) = Pos (l-1) (c-1)

-- ---------------------------------------------------------------------
-- | A ModuleCache is valid for the lifetime of a CachedModule
-- It is generated on need and the cache is invalidated
-- when a new CachedModule is loaded.
-- Allows the caching of arbitary data linked to a particular
-- TypecheckedModule.
-- TODO: this name is confusing, given GhcModuleCache. Change it
class Typeable a => ModuleCache a where
    -- | Defines an initial value for the state extension
    cacheDataProducer :: (MonadIO m) => CachedModule -> m a

instance ModuleCache () where
    cacheDataProducer = const $ return ()

