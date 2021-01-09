{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Nix.Effects.Basic where

import           Control.Monad
import           Control.Monad.State.Strict
import           Data.HashMap.Lazy              ( HashMap )
import qualified Data.HashMap.Lazy             as M
import           Data.List
import           Data.List.Split
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import           Data.Text.Prettyprint.Doc
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
import           Nix.Utils
import           Nix.Value
import           Nix.Value.Monad
import           System.FilePath

#ifdef MIN_VERSION_ghc_datasize
#if MIN_VERSION_ghc_datasize(0,2,0)
import           GHC.DataSize
#endif
#endif

defaultMakeAbsolutePath :: MonadNix e t f m => FilePath -> m FilePath
defaultMakeAbsolutePath origPath = do
  origPathExpanded <- expandHomePath origPath
  absPath          <- if isAbsolute origPathExpanded
    then pure origPathExpanded
    else do
      cwd <- do
        mres <- lookupVar "__cur_file"
        case mres of
          Nothing -> getCurrentDirectory
          Just v  -> demand v $ \case
            NVPath s -> pure $ takeDirectory s
            val ->
              throwError
                $  ErrorCall
                $  "when resolving relative path,"
                ++ " __cur_file is in scope,"
                ++ " but is not a path; it is: "
                ++ show val
      pure $ cwd <///> origPathExpanded
  removeDotDotIndirections <$> canonicalizePath absPath

expandHomePath :: MonadFile m => FilePath -> m FilePath
expandHomePath ('~' : xs) = flip (++) xs <$> getHomeDirectory
expandHomePath p          = pure p

-- | Incorrectly normalize paths by rewriting patterns like @a/b/..@ to @a@.
--   This is incorrect on POSIX systems, because if @b@ is a symlink, its
--   parent may be a different directory from @a@. See the discussion at
--   https://hackage.haskell.org/package/directory-1.3.1.5/docs/System-Directory.html#v:canonicalizePath
removeDotDotIndirections :: FilePath -> FilePath
removeDotDotIndirections = intercalate "/" . go [] . splitOn "/"
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
      [ xs ++ drop (length tx) ys | tx <- tails xs, tx `elem` inits ys ]

defaultFindEnvPath :: MonadNix e t f m => String -> m FilePath
defaultFindEnvPath = findEnvPathM

findEnvPathM :: forall e t f m . MonadNix e t f m => FilePath -> m FilePath
findEnvPathM name = do
  mres <- lookupVar "__nixPath"
  case mres of
    Nothing -> error "impossible"
    Just x  -> demand x $ fromValue >=> \(l :: [NValue t f m]) ->
      findPathBy nixFilePath l name
 where
  nixFilePath :: MonadEffects t f m => FilePath -> m (Maybe FilePath)
  nixFilePath path = do
    absPath <- makeAbsolutePath @t @f path
    isDir   <- doesDirectoryExist absPath
    absFile <- if isDir
      then makeAbsolutePath @t @f $ absPath </> "default.nix"
      else return absPath
    exists <- doesFileExist absFile
    pure $ if exists then Just absFile else Nothing

findPathBy
  :: forall e t f m
   . MonadNix e t f m
  => (FilePath -> m (Maybe FilePath))
  -> [NValue t f m]
  -> FilePath
  -> m FilePath
findPathBy finder ls name = do
  mpath <- foldM go Nothing ls
  case mpath of
    Nothing ->
      throwError
        $  ErrorCall
        $  "file '"
        ++ name
        ++ "' was not found in the Nix search path"
        ++ " (add it's using $NIX_PATH or -I)"
    Just path -> pure path
 where
  go :: Maybe FilePath -> NValue t f m -> m (Maybe FilePath)
  go p@(Just _) _ = pure p
  go Nothing l =
    demand l $ fromValue >=> \(s :: HashMap VarName (NValue t f m)) -> do
      p <- resolvePath s
      demand p $ fromValue >=> \(Path path) -> case M.lookup "prefix" s of
        Nothing -> tryPath path Nothing
        Just pf -> demand pf $ fromValueMay >=> \case
          Just (nsPfx :: NixString) ->
            let pfx = stringIgnoreContext nsPfx
            in  if not (Text.null pfx)
                  then tryPath path (Just (Text.unpack pfx))
                  else tryPath path Nothing
          _ -> tryPath path Nothing

  tryPath p (Just n) | n' : ns <- splitDirectories name, n == n' =
    finder $ p <///> joinPath ns
  tryPath p _ = finder $ p <///> name

  resolvePath s = case M.lookup "path" s of
    Just t  -> pure t
    Nothing -> case M.lookup "uri" s of
      Just ut -> defer $ fetchTarball ut
      Nothing ->
        throwError
          $  ErrorCall
          $  "__nixPath must be a list of attr sets"
          ++ " with 'path' elements, but received: "
          ++ show s

fetchTarball
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
fetchTarball = flip demand $ \case
  NVSet s _ -> case M.lookup "url" s of
    Nothing ->
      throwError $ ErrorCall "builtins.fetchTarball: Missing url attribute"
    Just url -> demand url $ go (M.lookup "sha256" s)
  v@NVStr{} -> go Nothing v
  v ->
    throwError
      $  ErrorCall
      $  "builtins.fetchTarball: Expected URI or set, got "
      ++ show v
 where
  go :: Maybe (NValue t f m) -> NValue t f m -> m (NValue t f m)
  go msha = \case
    NVStr ns -> fetch (stringIgnoreContext ns) msha
    v ->
      throwError
        $  ErrorCall
        $  "builtins.fetchTarball: Expected URI or string, got "
        ++ show v

{- jww (2018-04-11): This should be written using pipes in another module
    fetch :: Text -> Maybe (NThunk m) -> m (NValue t f m)
    fetch uri msha = case takeExtension (Text.unpack uri) of
        ".tgz" -> undefined
        ".gz"  -> undefined
        ".bz2" -> undefined
        ".xz"  -> undefined
        ".tar" -> undefined
        ext -> throwError $ ErrorCall $ "builtins.fetchTarball: Unsupported extension '"
                  ++ ext ++ "'"
-}

  fetch :: Text -> Maybe (NValue t f m) -> m (NValue t f m)
  fetch uri Nothing =
    nixInstantiateExpr $ "builtins.fetchTarball \"" ++ Text.unpack uri ++ "\""
  fetch url (Just t) = demand t $ fromValue >=> \nsSha ->
    let sha = stringIgnoreContext nsSha
    in  nixInstantiateExpr
          $  "builtins.fetchTarball { "
          ++ "url    = \""
          ++ Text.unpack url
          ++ "\"; "
          ++ "sha256 = \""
          ++ Text.unpack sha
          ++ "\"; }"

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
  existingPath path = do
    apath  <- makeAbsolutePath @t @f path
    exists <- doesPathExist apath
    pure $ if exists then Just apath else Nothing

defaultImportPath
  :: (MonadNix e t f m, MonadState (HashMap FilePath NExprLoc, b) m)
  => FilePath
  -> m (NValue t f m)
defaultImportPath path = do
  traceM $ "Importing file " ++ path
  withFrame Info (ErrorCall $ "While importing file " ++ show path) $ do
    imports <- gets fst
    evalExprLoc =<< case M.lookup path imports of
      Just expr -> pure expr
      Nothing   -> do
        eres <- parseNixFileLoc path
        case eres of
          Failure err ->
            throwError
              $ ErrorCall
              . show $ fillSep ["Parse during import failed:", err]
          Success expr -> do
            modify (\(a, b) -> (M.insert path expr a, b))
            pure expr

defaultPathToDefaultNix :: MonadNix e t f m => FilePath -> m FilePath
defaultPathToDefaultNix = pathToDefaultNixFile

-- Given a path, determine the nix file to load
pathToDefaultNixFile :: MonadFile m => FilePath -> m FilePath
pathToDefaultNixFile p = do
  isDir <- doesDirectoryExist p
  pure $ if isDir then p </> "default.nix" else p

defaultTraceEffect :: MonadPutStr m => String -> m ()
defaultTraceEffect = Nix.Effects.putStrLn
