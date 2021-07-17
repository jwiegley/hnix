{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PackageImports #-} -- 2021-07-05: Due to hashing Haskell IT system situation, in HNix we currently ended-up with 2 hash package dependencies @{hashing, cryptonite}@

{-# OPTIONS_GHC -Wno-orphans #-}


module Nix.Effects where

import           Prelude                 hiding ( traceM
                                                , putStr
                                                , putStrLn
                                                , print
                                                )
import qualified Prelude
import           Nix.Utils
import qualified Data.HashSet                  as HS
import qualified Data.Text                     as Text
import           Network.HTTP.Client     hiding ( path, Proxy )
import           Network.HTTP.Client.TLS
import           Network.HTTP.Types
import qualified "cryptonite" Crypto.Hash      as Hash
import           Nix.Utils.Fix1
import           Nix.Expr
import           Nix.Frames              hiding ( Proxy )
import           Nix.Parser
import           Nix.Render
import           Nix.Value
import qualified Paths_hnix
import           System.Exit
import           System.FilePath                ( takeFileName )
import qualified System.Info
import           System.Process

import qualified System.Nix.Store.Remote       as Store.Remote
import qualified System.Nix.StorePath          as Store

-- | A path into the nix store
newtype StorePath = StorePath FilePath


-- All of the following type classes defer to the underlying 'm'.

-- * @class MonadEffects t f m@

class
  ( MonadFile m
  , MonadStore m
  , MonadPutStr m
  , MonadHttp m
  , MonadEnv m
  , MonadPaths m
  , MonadInstantiate m
  , MonadExec m
  , MonadIntrospect m
  )
  => MonadEffects t f m where

  -- | Determine the absolute path of relative path in the current context
  makeAbsolutePath :: FilePath -> m FilePath
  findEnvPath :: String -> m FilePath

  -- | Having an explicit list of sets corresponding to the NIX_PATH
  -- and a file path try to find an existing path
  findPath :: [NValue t f m] -> FilePath -> m FilePath

  importPath :: FilePath -> m (NValue t f m)
  pathToDefaultNix :: FilePath -> m FilePath

  derivationStrict :: NValue t f m -> m (NValue t f m)

  --  2021-04-01: for trace, so leaving String here
  traceEffect :: String -> m ()


-- ** Instances

instance
  ( MonadFix1T t m
  , MonadStore m
  )
  => MonadStore (Fix1T t m)
 where
  addToStore a b c d = lift $ addToStore a b c d
  addTextToStore' a b c d = lift $ addTextToStore' a b c d

-- * @class MonadIntrospect m@

class
  Monad m
  => MonadIntrospect m
 where
  recursiveSize :: a -> m Word
  default recursiveSize :: (MonadTrans t, MonadIntrospect m', m ~ t m') => a -> m Word
  recursiveSize = lift . recursiveSize


-- ** Instances

instance MonadIntrospect IO where
  recursiveSize =
#ifdef MIN_VERSION_ghc_datasize
    recursiveSize
#else
    \_ -> pure 0
#endif

deriving
  instance
    MonadIntrospect (t (Fix1 t))
    => MonadIntrospect (Fix1 t)

deriving
  instance
    MonadIntrospect (t (Fix1T t m) m)
    => MonadIntrospect (Fix1T t m)


-- * @class MonadExec m@

class
  Monad m
  => MonadExec m where

    exec' :: [Text] -> m (Either ErrorCall NExprLoc)
    default exec' :: (MonadTrans t, MonadExec m', m ~ t m')
                  => [Text] -> m (Either ErrorCall NExprLoc)
    exec' = lift . exec'


-- ** Instances

instance MonadExec IO where
  exec' = \case
    []            -> pure $ Left $ ErrorCall "exec: missing program"
    (prog : args) -> do
      (exitCode, out, _) <- liftIO $ readProcessWithExitCode (toString prog) (toString <$> args) ""
      let
        t    = Text.strip $ toText out
        emsg = "program[" <> prog <> "] args=" <> show args
      case exitCode of
        ExitSuccess ->
          pure $
          if Text.null t
            then Left $ ErrorCall $ toString $ "exec has no output :" <> emsg
            else
              either
                (\ err -> Left $ ErrorCall $ toString $ "Error parsing output of exec: " <> show err <> " " <> emsg)
                pure
                (parseNixTextLoc t)
        err -> pure $ Left $ ErrorCall $ toString $ "exec  failed: " <> show err <> " " <> emsg

deriving
  instance
    MonadExec (t (Fix1 t))
    => MonadExec (Fix1 t)

deriving
  instance
    MonadExec (t (Fix1T t m) m)
    => MonadExec (Fix1T t m)


-- * @class MonadInstantiate m@

class
  Monad m
  => MonadInstantiate m where

    instantiateExpr :: Text -> m (Either ErrorCall NExprLoc)
    default instantiateExpr :: (MonadTrans t, MonadInstantiate m', m ~ t m') => Text -> m (Either ErrorCall NExprLoc)
    instantiateExpr = lift . instantiateExpr


-- ** Instances

instance MonadInstantiate IO where

  instantiateExpr expr =
    do
      traceM $
        "Executing: " <> show ["nix-instantiate", "--eval", "--expr ", expr]

      (exitCode, out, err) <-
        readProcessWithExitCode
          "nix-instantiate"
          ["--eval", "--expr", toString expr]
          ""

      pure $
        case exitCode of
          ExitSuccess ->
            either
              (\ e -> Left $ ErrorCall $ "Error parsing output of nix-instantiate: " <> show e)
              pure
              (parseNixTextLoc $ toText out)
          status -> Left $ ErrorCall $ "nix-instantiate failed: " <> show status <> ": " <> err

deriving
  instance
    MonadInstantiate (t (Fix1 t))
    => MonadInstantiate (Fix1 t)

deriving
  instance
    MonadInstantiate (t (Fix1T t m) m)
    => MonadInstantiate (Fix1T t m)


-- * @class MonadEnv m@

class
  Monad m
  => MonadEnv m where

  getEnvVar :: Text -> m (Maybe Text)
  default getEnvVar :: (MonadTrans t, MonadEnv m', m ~ t m') => Text -> m (Maybe Text)
  getEnvVar = lift . getEnvVar

  getCurrentSystemOS :: m Text
  default getCurrentSystemOS :: (MonadTrans t, MonadEnv m', m ~ t m') => m Text
  getCurrentSystemOS = lift getCurrentSystemOS

  getCurrentSystemArch :: m Text
  default getCurrentSystemArch :: (MonadTrans t, MonadEnv m', m ~ t m') => m Text
  getCurrentSystemArch = lift getCurrentSystemArch


-- ** Instances

instance MonadEnv IO where
  getEnvVar            = (<<$>>) toText . lookupEnv . toString

  getCurrentSystemOS   = pure $ toText System.Info.os

  -- Invert the conversion done by GHC_CONVERT_CPU in GHC's aclocal.m4
  getCurrentSystemArch = pure $ toText $ case System.Info.arch of
    "i386" -> "i686"
    arch   -> arch

deriving
  instance
    MonadEnv (t (Fix1 t))
    => MonadEnv (Fix1 t)

deriving
  instance
    MonadEnv (t (Fix1T t m) m)
    => MonadEnv (Fix1T t m)


-- * @class MonadPaths m@

class
  Monad m
  => MonadPaths m where
  getDataDir :: m FilePath
  default getDataDir :: (MonadTrans t, MonadPaths m', m ~ t m') => m FilePath
  getDataDir = lift getDataDir


-- ** Instances

instance MonadPaths IO where
  getDataDir = Paths_hnix.getDataDir

deriving
  instance
    MonadPaths (t (Fix1 t))
    => MonadPaths (Fix1 t)

deriving
  instance
    MonadPaths (t (Fix1T t m) m)
    => MonadPaths (Fix1T t m)


-- * @class MonadHttp m@

class
  Monad m
  => MonadHttp m where

  getURL :: Text -> m (Either ErrorCall StorePath)
  default getURL :: (MonadTrans t, MonadHttp m', m ~ t m') => Text -> m (Either ErrorCall StorePath)
  getURL = lift . getURL


-- ** Instances

instance MonadHttp IO where
  getURL url = do
    let urlstr = toString url
    traceM $ "fetching HTTP URL: " <> urlstr
    req     <- parseRequest urlstr
    manager <-
      if secure req
        then newTlsManager
        else newManager defaultManagerSettings
    -- print req
    response <- httpLbs (req { method = "GET" }) manager
    let status = statusCode $ responseStatus response
    pure $ Left $ ErrorCall $ if status /= 200
      then
        "fail, got " <> show status <> " when fetching url:" <> urlstr
      else
        -- do
        -- let bstr = responseBody response
        "success in downloading but hnix-store is not yet ready; url = " <> urlstr

deriving
  instance
    MonadHttp (t (Fix1 t))
    => MonadHttp (Fix1 t)

deriving
  instance
    MonadHttp (t (Fix1T t m) m)
    => MonadHttp (Fix1T t m)


-- * @class MonadPutStr m@

class
  Monad m
  => MonadPutStr m where

  --TODO: Should this be used *only* when the Nix to be evaluated invokes a
  --`trace` operation?
  --  2021-04-01: Due to trace operation here, leaving it as String.
  putStr :: String -> m ()
  default putStr :: (MonadTrans t, MonadPutStr m', m ~ t m') => String -> m ()
  putStr = lift . putStr


-- ** Instances

instance MonadPutStr IO where
  putStr = Prelude.putStr

deriving
  instance
    MonadPutStr (t (Fix1 t))
    => MonadPutStr (Fix1 t)

deriving
  instance
    MonadPutStr (t (Fix1T t m) m)
    => MonadPutStr (Fix1T t m)


-- ** Functions

putStrLn :: MonadPutStr m => String -> m ()
putStrLn = putStr . (<> "\n")

print :: (MonadPutStr m, Show a) => a -> m ()
print = putStrLn . show

-- * Store effects

-- ** Data type synonyms

type RecursiveFlag = Bool
type RepairFlag = Bool
type StorePathName = Text
type FilePathFilter m = FilePath -> m Bool
type StorePathSet = HS.HashSet StorePath

-- ** @class MonadStore m@

class
  Monad m
  => MonadStore m where

  -- | Copy the contents of a local path to the store.  The resulting store
  -- path is returned.  Note: This does not support yet support the expected
  -- `filter` function that allows excluding some files.
  addToStore :: StorePathName -> FilePath -> RecursiveFlag -> RepairFlag -> m (Either ErrorCall StorePath)
  default addToStore :: (MonadTrans t, MonadStore m', m ~ t m') => StorePathName -> FilePath -> RecursiveFlag -> RepairFlag -> m (Either ErrorCall StorePath)
  addToStore a b c d = lift $ addToStore a b c d

  -- | Like addToStore, but the contents written to the output path is a
  -- regular file containing the given string.
  addTextToStore' :: StorePathName -> Text -> Store.StorePathSet -> RepairFlag -> m (Either ErrorCall StorePath)
  default addTextToStore' :: (MonadTrans t, MonadStore m', m ~ t m') => StorePathName -> Text -> Store.StorePathSet -> RepairFlag -> m (Either ErrorCall StorePath)
  addTextToStore' a b c d = lift $ addTextToStore' a b c d


-- *** Instances

instance MonadStore IO where

  addToStore name path recursive repair =
    either
      (\ err -> pure $ Left $ ErrorCall $ "String '" <> show name <> "' is not a valid path name: " <> err)
      (\ pathName ->
        do
          -- TODO: redesign the filter parameter
          res <- Store.Remote.runStore $ Store.Remote.addToStore @Hash.SHA256 pathName path recursive (const False) repair
          either
            Left -- err
            (pure . StorePath . decodeUtf8 . Store.storePathToRawFilePath) -- store path
            <$> parseStoreResult "addToStore" res
      )
      (Store.makeStorePathName name)

  addTextToStore' name text references repair =
    do
      res <- Store.Remote.runStore $ Store.Remote.addTextToStore name text references repair
      either
        Left -- err
        (pure . StorePath . decodeUtf8 . Store.storePathToRawFilePath) -- path
        <$> parseStoreResult "addTextToStore" res


-- ** Functions

parseStoreResult :: Monad m => Text -> (Either String a, [Store.Remote.Logger]) -> m (Either ErrorCall a)
parseStoreResult name res =
  pure $ either
    (\ msg -> Left $ ErrorCall $ "Failed to execute '" <> toString name <> "': " <> msg <> "\n" <> show logs)
    pure -- result
    (fst res)
 where
  logs = snd res

addTextToStore :: (Framed e m, MonadStore m) => StorePathName -> Text -> Store.StorePathSet -> RepairFlag -> m StorePath
addTextToStore a b c d =
  either
    throwError
    pure
    =<< addTextToStore' a b c d

addPath :: (Framed e m, MonadStore m) => FilePath -> m StorePath
addPath p =
  either
    throwError
    pure
    =<< addToStore (toText $ takeFileName p) p True False

toFile_ :: (Framed e m, MonadStore m) => FilePath -> String -> m StorePath
toFile_ p contents = addTextToStore (toText p) (toText contents) mempty False
