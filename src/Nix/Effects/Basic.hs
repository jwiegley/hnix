{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Nix.Effects.Basic where

import           Prelude                 hiding ( traceM
                                                , head
                                                )
import           Relude.Unsafe                  ( head )
import           Nix.Utils
import           Control.Monad                  ( foldM )
import qualified Data.HashMap.Lazy             as M
import           Data.List.Split                ( splitOn )
import qualified Data.Text                     as Text
import           Data.Text.Prettyprint.Doc      ( fillSep )
import           System.FilePath
import           Nix.Convert
import           Nix.Effects
import           Nix.Exec                       ( MonadNix
                                                , evalExprLoc
                                                , nixInstantiateExpr
                                                )
import           Nix.Expr
import           Nix.Frames
import           Nix.Parser
import           Nix.Render
import           Nix.Scope
import           Nix.String
import           Nix.Value
import           Nix.Value.Monad

#ifdef MIN_VERSION_ghc_datasize
import           GHC.DataSize
#endif

defaultMakeAbsolutePath :: MonadNix e t f m => FilePath -> m FilePath
defaultMakeAbsolutePath origPath = do
  origPathExpanded <- expandHomePath origPath
  absPath          <-
    bool
      (do
        cwd <- do
          mres <- lookupVar "__cur_file"
          maybe
            getCurrentDirectory
            (
              (\case
                NVPath s -> pure $ takeDirectory s
                val -> throwError $ ErrorCall $ "when resolving relative path, __cur_file is in scope, but is not a path; it is: " <> show val
              ) <=< demand
            )
            mres
        pure $ cwd <///> origPathExpanded
      )
      (pure origPathExpanded)
      (isAbsolute origPathExpanded)
  removeDotDotIndirections <$> canonicalizePath absPath

expandHomePath :: MonadFile m => FilePath -> m FilePath
expandHomePath ('~' : xs) = (<> xs) <$> getHomeDirectory
expandHomePath p          = pure p

-- | Incorrectly normalize paths by rewriting patterns like @a/b/..@ to @a@.
--   This is incorrect on POSIX systems, because if @b@ is a symlink, its
--   parent may be a different directory from @a@. See the discussion at
--   https://hackage.haskell.org/package/directory-1.3.1.5/docs/System-Directory.html#v:canonicalizePath
removeDotDotIndirections :: FilePath -> FilePath
removeDotDotIndirections = intercalate "/" . go mempty . splitOn "/"
 where
  go s       []            = reverse s
  go (_ : s) (".." : rest) = go s rest
  go s       (this : rest) = go (this : s) rest

infixr 9 <///>
(<///>) :: FilePath -> FilePath -> FilePath
x <///> y | isAbsolute y || "." `isPrefixOf` y = x </> y
          | otherwise                          = joinByLargestOverlap x y
 where
  joinByLargestOverlap (splitDirectories -> xs) (splitDirectories -> ys) =
    joinPath $ head
      [ xs <> drop (length tx) ys | tx <- tails xs, tx `elem` inits ys ]

defaultFindEnvPath :: MonadNix e t f m => String -> m FilePath
defaultFindEnvPath = findEnvPathM

findEnvPathM :: forall e t f m . MonadNix e t f m => FilePath -> m FilePath
findEnvPathM name = do
  mres <- lookupVar "__nixPath"

  maybe
    (fail "impossible")
    (
      (\ nv ->
        do
          (l :: [NValue t f m]) <- fromValue nv
          findPathBy nixFilePath l name
      ) <=< demand
    )
    mres

 where
  nixFilePath :: MonadEffects t f m => FilePath -> m (Maybe FilePath)
  nixFilePath path = do
    absPath <- makeAbsolutePath @t @f path
    isDir   <- doesDirectoryExist absPath
    absFile <-
      bool
        (pure absPath)
        (makeAbsolutePath @t @f $ absPath </> "default.nix")
        isDir
    exists <- doesFileExist absFile
    pure $
      bool
        mempty
        (pure absFile)
        exists

findPathBy
  :: forall e t f m
   . MonadNix e t f m
  => (FilePath -> m (Maybe FilePath))
  -> [NValue t f m]
  -> FilePath
  -> m FilePath
findPathBy finder ls name = do
  mpath <- foldM go mempty ls
  maybe
    (throwError $ ErrorCall $ "file ''" <> name <> "'' was not found in the Nix search path (add it's using $NIX_PATH or -I)")
    pure
    mpath
 where
  go :: MonadNix e t f m => Maybe FilePath -> NValue t f m -> m (Maybe FilePath)
  go mp =
    maybe
      (\ nv ->
        do
          (s :: HashMap VarName (NValue t f m)) <- fromValue =<< demand nv
          p <- resolvePath s
          nvpath <- demand p
          (Path path) <- fromValue nvpath

          maybe
            (tryPath path mempty)
            (\ nv' ->
              do
                mns <- fromValueMay =<< demand nv'
                tryPath path $
                  case mns of
                    Just (nsPfx :: NixString) ->
                      let pfx = stringIgnoreContext nsPfx in
                      bool
                        mempty
                        (pure (toString pfx))
                        (not $ Text.null pfx)
                    _ -> mempty
            )
            (M.lookup "prefix" s)
      )
      (const . pure . pure)
      mp

  tryPath :: FilePath -> Maybe FilePath -> m (Maybe FilePath)
  tryPath p (Just n) | n' : ns <- splitDirectories name, n == n' =
    finder $ p <///> joinPath ns
  tryPath p _ = finder $ p <///> name

  resolvePath s =
    maybe
      (maybe
        (throwError $ ErrorCall $ "__nixPath must be a list of attr sets with 'path' elements, but received: " <> show s)
        (defer . fetchTarball)
        (M.lookup "uri" s)
      )
      pure
      (M.lookup "path" s)

fetchTarball
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
fetchTarball =
  \case
    NVSet _ s ->
      maybe
        (throwError $ ErrorCall "builtins.fetchTarball: Missing url attribute")
        (go (M.lookup "sha256" s) <=< demand)
        (M.lookup "url" s)
    v@NVStr{} -> go Nothing v
    v -> throwError $ ErrorCall $ "builtins.fetchTarball: Expected URI or set, got " <> show v
  <=< demand
 where
  go :: Maybe (NValue t f m) -> NValue t f m -> m (NValue t f m)
  go msha = \case
    NVStr ns -> fetch (stringIgnoreContext ns) msha
    v -> throwError $ ErrorCall $ "builtins.fetchTarball: Expected URI or string, got " <> show v

{- jww (2018-04-11): This should be written using pipes in another module
    fetch :: Text -> Maybe (NThunk m) -> m (NValue t f m)
    fetch uri msha = case takeExtension uri of
        ".tgz" -> undefined
        ".gz"  -> undefined
        ".bz2" -> undefined
        ".xz"  -> undefined
        ".tar" -> undefined
        ext -> throwError $ ErrorCall $ "builtins.fetchTarball: Unsupported extension '"
                  <> ext <> "'"
-}

  fetch :: Text -> Maybe (NValue t f m) -> m (NValue t f m)
  fetch uri Nothing =
    nixInstantiateExpr $ "builtins.fetchTarball \"" <> uri <> "\""
  fetch url (Just t) =
      (\nv -> do
        nsSha <- fromValue nv

        let sha = stringIgnoreContext nsSha

        nixInstantiateExpr
          $ "builtins.fetchTarball { " <> "url    = \"" <> url <> "\"; " <> "sha256 = \"" <> sha <> "\"; }"
      ) =<< demand t

defaultFindPath :: MonadNix e t f m => [NValue t f m] -> FilePath -> m FilePath
defaultFindPath = findPathM

findPathM
  :: forall e t f m
   . MonadNix e t f m
  => [NValue t f m]
  -> FilePath
  -> m FilePath
findPathM = findPathBy existingPath
 where
  existingPath :: MonadEffects t f m => FilePath -> m (Maybe FilePath)
  existingPath path =
    do
      apath  <- makeAbsolutePath @t @f path
      doesExist <- doesPathExist apath
      pure $ pure apath `whenTrue` doesExist

defaultImportPath
  :: (MonadNix e t f m, MonadState (HashMap FilePath NExprLoc, b) m)
  => FilePath
  -> m (NValue t f m)
defaultImportPath path = do
  traceM $ "Importing file " <> path
  withFrame Info (ErrorCall $ "While importing file " <> show path) $ do
    imports <- gets fst
    evalExprLoc =<<
      maybe
        (do
          eres <- parseNixFileLoc path
          either
            (\ err -> throwError $ ErrorCall . show $ fillSep ["Parse during import failed:", err])
            (\ expr ->
              do
                modify (first (M.insert path expr))
                pure expr
            )
            eres
        )
        pure  -- return expr
        (M.lookup path imports)

defaultPathToDefaultNix :: MonadNix e t f m => FilePath -> m FilePath
defaultPathToDefaultNix = pathToDefaultNixFile

-- Given a path, determine the nix file to load
pathToDefaultNixFile :: MonadFile m => FilePath -> m FilePath
pathToDefaultNixFile p = do
  isDir <- doesDirectoryExist p
  pure $ p </> "default.nix" `whenTrue` isDir

defaultTraceEffect :: MonadPutStr m => String -> m ()
defaultTraceEffect = Nix.Effects.putStrLn
