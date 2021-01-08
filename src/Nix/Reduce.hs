{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module provides a "reducing" expression evaluator, which reduces
--   away pure, non self-referential aspects of an expression tree, yielding a
--   new expression tree. It does not yet attempt to reduce everything
--   possible, and will always yield a tree with the same meaning as the
--   original. It should be seen as an opportunistic simplifier, but which
--   gives up easily if faced with any potential for ambiguity in the result.

module Nix.Reduce (reduceExpr, reducingEvalExpr) where

import           Control.Applicative
import           Control.Arrow                  ( second )
import           Control.Monad
import           Control.Monad.Catch
#if !MIN_VERSION_base(4,13,0)
import           Control.Monad.Fail
#endif
import           Control.Monad.Fix
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.Fix                       ( Fix(..), foldFix, foldFixM )
import           Data.HashMap.Lazy              ( HashMap )
import qualified Data.HashMap.Lazy             as M
import qualified Data.HashMap.Strict           as MS
import           Data.IORef
import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty            as NE
import           Data.Maybe                     ( fromMaybe
                                                , mapMaybe
                                                , catMaybes
                                                )
import           Data.Text                      ( Text )
import           Nix.Atoms
import           Nix.Effects.Basic              ( pathToDefaultNixFile )
import           Nix.Expr
import           Nix.Frames
import           Nix.Options                    ( Options
                                                , reduceSets
                                                , reduceLists
                                                )
import           Nix.Parser
import           Nix.Scope
import           Nix.Utils
import           System.Directory
import           System.FilePath

newtype Reducer m a = Reducer
    { runReducer :: ReaderT (Maybe FilePath, Scopes (Reducer m) NExprLoc)
                           (StateT (HashMap FilePath NExprLoc, MS.HashMap Text Text) m) a }
    deriving (Functor, Applicative, Alternative, Monad, MonadPlus,
              MonadFix, MonadIO, MonadFail,
              MonadReader (Maybe FilePath, Scopes (Reducer m) NExprLoc),
              MonadState (HashMap FilePath NExprLoc, MS.HashMap Text Text))

staticImport
  :: forall m
   . ( MonadIO m
     , Scoped m NExprLoc m
     , MonadFail m
     , MonadReader (Maybe FilePath, Scopes m NExprLoc) m
     , MonadState (HashMap FilePath NExprLoc, HashMap Text Text) m
     )
  => SrcSpan
  -> FilePath
  -> m NExprLoc
staticImport pann path = do
  mfile <- asks fst
  path  <- liftIO $ pathToDefaultNixFile path
  path' <- liftIO $ pathToDefaultNixFile =<< canonicalizePath
    (maybe path (\p -> takeDirectory p </> path) mfile)

  imports <- gets fst
  case M.lookup path' imports of
    Just expr -> pure expr
    Nothing   -> go path'
 where
  go path = do
    liftIO $ putStrLn $ "Importing file " ++ path

    eres <- liftIO $ parseNixFileLoc path
    case eres of
      Failure err -> error $ "Parse failed: " ++ show err
      Success x   -> do
        let
          pos  = SourcePos "Reduce.hs" (mkPos 1) (mkPos 1)
          span = SrcSpan pos pos
          cur  = NamedVar (StaticKey "__cur_file" :| [])
                          (Fix (NLiteralPath_ pann path))
                          pos
          x' = Fix (NLet_ span [cur] x)
        modify (\(a, b) -> (M.insert path x' a, b))
        local (const (Just path, emptyScopes @m @NExprLoc)) $ do
          x'' <- foldFix reduce x'
          modify (\(a, b) -> (M.insert path x'' a, b))
          return x''

-- gatherNames :: NExprLoc -> HashSet VarName
-- gatherNames = foldFix $ \case
--     NSym_ _ var -> S.singleton var
--     Compose (Ann _ x) -> fold x

reduceExpr
  :: (MonadIO m, MonadFail m) => Maybe FilePath -> NExprLoc -> m NExprLoc
reduceExpr mpath expr =
  (`evalStateT` (M.empty, MS.empty))
    . (`runReaderT` (mpath, emptyScopes))
    . runReducer
    $ foldFix reduce expr

reduce
  :: forall m
   . ( MonadIO m
     , Scoped m NExprLoc m
     , MonadFail m
     , MonadReader (Maybe FilePath, Scopes m NExprLoc) m
     , MonadState (HashMap FilePath NExprLoc, MS.HashMap Text Text) m
     )
  => NExprLocF (m NExprLoc)
  -> m NExprLoc

-- | Reduce the variable to its value if defined.
--   Leave it as it is otherwise.
reduce (NSym_ ann var) = lookupVar var <&> \case
  Nothing -> Fix (NSym_ ann var)
  Just v  -> v

-- | Reduce binary and integer negation.
reduce (NUnary_ uann op arg) = arg >>= \x -> case (op, x) of
  (NNeg, Fix (NConstant_ cann (NInt n))) ->
    return $ Fix $ NConstant_ cann (NInt (negate n))
  (NNot, Fix (NConstant_ cann (NBool b))) ->
    return $ Fix $ NConstant_ cann (NBool (not b))
  _ -> return $ Fix $ NUnary_ uann op x

-- | Reduce function applications.
--
--     * Reduce an import to the actual imported expression.
--
--     * Reduce a lambda function by adding its name to the local
--       scope and recursively reducing its body.
reduce (NBinary_ bann NApp fun arg) = fun >>= \case
  f@(Fix (NSym_ _ "import")) -> arg >>= \case
      -- Fix (NEnvPath_     pann origPath) -> staticImport pann origPath
    Fix (NLiteralPath_ pann origPath) -> staticImport pann origPath
    v -> return $ Fix $ NBinary_ bann NApp f v

  Fix (NAbs_ _ (Param name) body) -> do
    x <- arg
    pushScope (M.singleton name x) (foldFix reduce body)

  f -> Fix . NBinary_ bann NApp f <$> arg

-- | Reduce an integer addition to its result.
reduce (NBinary_ bann op larg rarg) = do
  lval <- larg
  rval <- rarg
  case (op, lval, rval) of
    (NPlus, Fix (NConstant_ ann (NInt x)), Fix (NConstant_ _ (NInt y))) ->
      return $ Fix (NConstant_ ann (NInt (x + y)))
    _ -> pure $ Fix $ NBinary_ bann op lval rval

-- | Reduce a select on a Set by substituting the set to the selected value.
--
-- Before applying this reduction, we need to ensure that:
--
--   1. The selected expr is indeed a set.
--   2. The selection AttrPath is a list of StaticKeys.
--   3. The selected AttrPath exists in the set.
reduce base@(NSelect_ _ _ attrs _)
  | sAttrPath $ NE.toList attrs = do
    (NSelect_ _ aset attrs _) <- sequence base
    inspectSet (unFix aset) attrs
  | otherwise = sId
 where
  sId = Fix <$> sequence base
  -- The selection AttrPath is composed of StaticKeys.
  sAttrPath (StaticKey _ : xs) = sAttrPath xs
  sAttrPath []                 = True
  sAttrPath _                  = False
  -- Find appropriate bind in set's binds.
  findBind []       _              = Nothing
  findBind (x : xs) attrs@(a :| _) = case x of
    n@(NamedVar (a' :| _) _ _) | a' == a -> Just n
    _ -> findBind xs attrs
  -- Follow the attrpath recursively in sets.
  inspectSet (NSet_ _ NNonRecursive binds) attrs = case findBind binds attrs of
    Just (NamedVar _ e _) -> case NE.uncons attrs of
      (_, Just attrs) -> inspectSet (unFix e) attrs
      _               -> pure e
    _ -> sId
  inspectSet _ _ = sId

-- reduce (NHasAttr aset attr) =

-- | Reduce a set by inlining its binds outside of the set
--   if none of the binds inherit the super set.
reduce e@(NSet_ ann NNonRecursive binds) = do
  let usesInherit = flip any binds $ \case
        Inherit{} -> True
        _         -> False
  if usesInherit
    then clearScopes $ Fix . NSet_ ann NNonRecursive <$> traverse sequence binds
    else Fix <$> sequence e

-- Encountering a 'rec set' construction eliminates any hope of inlining
-- definitions.
reduce (NSet_ ann NRecursive binds) =
  clearScopes $ Fix . NSet_ ann NRecursive <$> traverse sequence binds

-- Encountering a 'with' construction eliminates any hope of inlining
-- definitions.
reduce (NWith_ ann scope body) =
  clearScopes $ fmap Fix $ NWith_ ann <$> scope <*> body

-- | Reduce a let binds section by pushing lambdas,
--   constants and strings to the body scope.
reduce (NLet_ ann binds body) = do
  s <- fmap (M.fromList . catMaybes) $ forM binds $ \case
    NamedVar (StaticKey name :| []) def _pos -> def >>= \case
      d@(Fix NAbs_{}     ) -> pure $ Just (name, d)
      d@(Fix NConstant_{}) -> pure $ Just (name, d)
      d@(Fix NStr_{}     ) -> pure $ Just (name, d)
      _                    -> pure Nothing
    _ -> pure Nothing
  body'  <- pushScope s body
  binds' <- traverse sequence binds
  -- let names = gatherNames body'
  -- binds' <- traverse sequence binds <&> \b -> flip filter b $ \case
  --     NamedVar (StaticKey name _ :| []) _ ->
  --         name `S.member` names
  --     _ -> True
  pure $ Fix $ NLet_ ann binds' body'
  -- where
  --   go m [] = pure m
  --   go m (x:xs) = case x of
  --       NamedVar (StaticKey name _ :| []) def -> do
  --           v <- pushScope m def
  --           go (M.insert name v m) xs
  --       _ -> go m xs

-- | Reduce an if to the relevant path if
--   the condition is a boolean constant.
reduce e@(NIf_ _ b t f) = b >>= \case
  Fix (NConstant_ _ (NBool b')) -> if b' then t else f
  _                             -> Fix <$> sequence e

-- | Reduce an assert atom to its encapsulated
--   symbol if the assertion is a boolean constant.
reduce e@(NAssert_ _ b body) = b >>= \case
  Fix (NConstant_ _ (NBool b')) | b' -> body
  _ -> Fix <$> sequence e

reduce (NAbs_ ann params body) = do
  params' <- sequence params
  -- Make sure that variable definitions in scope do not override function
  -- arguments.
  let args = case params' of
        Param name -> M.singleton name (Fix (NSym_ ann name))
        ParamSet pset _ _ ->
          M.fromList $ map (\(k, _) -> (k, Fix (NSym_ ann k))) pset
  Fix . NAbs_ ann params' <$> pushScope args body

reduce v = Fix <$> sequence v

-- newtype FlaggedF f r = FlaggedF { flagged :: (IORef Bool, f r) }
newtype FlaggedF f r = FlaggedF (IORef Bool, f r)
    deriving (Functor, Foldable, Traversable)

instance Show (f r) => Show (FlaggedF f r) where
  show (FlaggedF (_, x)) = show x

type Flagged f = Fix (FlaggedF f)

flagExprLoc :: (MonadIO n, Traversable f) => Fix f -> n (Flagged f)
flagExprLoc = foldFixM $ \x -> do
  flag <- liftIO $ newIORef False
  pure $ Fix $ FlaggedF (flag, x)

-- stripFlags :: Functor f => Flagged f -> Fix f
-- stripFlags = foldFix $ Fix . snd . flagged

pruneTree :: MonadIO n => Options -> Flagged NExprLocF -> n (Maybe NExprLoc)
pruneTree opts = foldFixM $ \(FlaggedF (b, Compose x)) -> do
  used <- liftIO $ readIORef b
  pure $ if used then Fix . Compose <$> traverse prune x else Nothing
 where
  prune :: NExprF (Maybe NExprLoc) -> Maybe (NExprF NExprLoc)
  prune = \case
    NStr str -> Just $ NStr (pruneString str)
    NHasAttr (Just aset) attr ->
      Just $ NHasAttr aset (NE.map pruneKeyName attr)
    NAbs params (Just body) -> Just $ NAbs (pruneParams params) body

    NList l | reduceLists opts -> Just $ NList (catMaybes l)
            | otherwise        -> Just $ NList (map (fromMaybe nNull) l)
    NSet recur binds
      | reduceSets opts -> Just $ NSet recur (mapMaybe sequence binds)
      | otherwise -> Just $ NSet recur (map (fmap (fromMaybe nNull)) binds)

    NLet binds (Just body@(Fix (Compose (Ann _ x)))) ->
      Just $ case mapMaybe pruneBinding binds of
        [] -> x
        xs -> NLet xs body

    NSelect (Just aset) attr alt ->
      Just $ NSelect aset (NE.map pruneKeyName attr) (join alt)

    -- These are the only short-circuiting binary operators
    NBinary NAnd (Just (Fix (Compose (Ann _ larg)))) _ -> Just larg
    NBinary NOr (Just (Fix (Compose (Ann _ larg)))) _ -> Just larg

    -- If the function was never called, it means its argument was in a
    -- thunk that was forced elsewhere.
    NBinary NApp Nothing (Just _) -> Nothing

    -- The idea behind emitted a binary operator where one side may be
    -- invalid is that we're trying to emit what will reproduce whatever
    -- error the user encountered, which means providing all aspects of
    -- the evaluation path they ultimately followed.
    NBinary op Nothing (Just rarg) -> Just $ NBinary op nNull rarg
    NBinary op (Just larg) Nothing -> Just $ NBinary op larg nNull

    -- If the scope of a with was never referenced, it's not needed
    NWith Nothing (Just (Fix (Compose (Ann _ body)))) -> Just body

    NAssert Nothing _ ->
      error "How can an assert be used, but its condition not?"

    NAssert _ (Just (Fix (Compose (Ann _ body)))) -> Just body
    NAssert (Just cond) _ -> Just $ NAssert cond nNull

    NIf Nothing _ _ -> error "How can an if be used, but its condition not?"

    NIf _ Nothing (Just (Fix (Compose (Ann _ f)))) -> Just f
    NIf _ (Just (Fix (Compose (Ann _ t)))) Nothing -> Just t

    x                     -> sequence x

  pruneString :: NString (Maybe NExprLoc) -> NString NExprLoc
  pruneString (DoubleQuoted xs) =
    DoubleQuoted (mapMaybe pruneAntiquotedText xs)
  pruneString (Indented n xs) = Indented n (mapMaybe pruneAntiquotedText xs)

  pruneAntiquotedText
    :: Antiquoted Text (Maybe NExprLoc) -> Maybe (Antiquoted Text NExprLoc)
  pruneAntiquotedText (Plain v)             = Just (Plain v)
  pruneAntiquotedText EscapedNewline        = Just EscapedNewline
  pruneAntiquotedText (Antiquoted Nothing ) = Nothing
  pruneAntiquotedText (Antiquoted (Just k)) = Just (Antiquoted k)

  pruneAntiquoted
    :: Antiquoted (NString (Maybe NExprLoc)) (Maybe NExprLoc)
    -> Maybe (Antiquoted (NString NExprLoc) NExprLoc)
  pruneAntiquoted (Plain v)             = Just (Plain (pruneString v))
  pruneAntiquoted EscapedNewline        = Just EscapedNewline
  pruneAntiquoted (Antiquoted Nothing ) = Nothing
  pruneAntiquoted (Antiquoted (Just k)) = Just (Antiquoted k)

  pruneKeyName :: NKeyName (Maybe NExprLoc) -> NKeyName NExprLoc
  pruneKeyName (StaticKey n) = StaticKey n
  pruneKeyName (DynamicKey k) | Just k' <- pruneAntiquoted k = DynamicKey k'
                              | otherwise = StaticKey "<unused?>"

  pruneParams :: Params (Maybe NExprLoc) -> Params NExprLoc
  pruneParams (Param n) = Param n
  pruneParams (ParamSet xs b n)
    | reduceSets opts = ParamSet
      (map (second (maybe (Just nNull) (Just . fromMaybe nNull))) xs)
      b
      n
    | otherwise = ParamSet (map (second (fmap (fromMaybe nNull))) xs) b n

  pruneBinding :: Binding (Maybe NExprLoc) -> Maybe (Binding NExprLoc)
  pruneBinding (NamedVar _ Nothing _) = Nothing
  pruneBinding (NamedVar xs (Just x) pos) =
    Just (NamedVar (NE.map pruneKeyName xs) x pos)
  pruneBinding (Inherit _                 [] _) = Nothing
  pruneBinding (Inherit (join -> Nothing) _  _) = Nothing
  pruneBinding (Inherit (join -> m) xs pos) =
    Just (Inherit m (map pruneKeyName xs) pos)

reducingEvalExpr
  :: (Framed e m, Has e Options, Exception r, MonadCatch m, MonadIO m)
  => (NExprLocF (m a) -> m a)
  -> Maybe FilePath
  -> NExprLoc
  -> m (NExprLoc, Either r a)
reducingEvalExpr eval mpath expr = do
  expr'           <- flagExprLoc =<< liftIO (reduceExpr mpath expr)
  eres <- catch (Right <$> foldFix (addEvalFlags eval) expr') (pure . Left)
  opts :: Options <- asks (view hasLens)
  expr''          <- pruneTree opts expr'
  return (fromMaybe nNull expr'', eres)
  where addEvalFlags k (FlaggedF (b, x)) = liftIO (writeIORef b True) *> k x

instance Monad m => Scoped (Reducer m) NExprLoc (Reducer m) where
  currentScopes = currentScopesReader
  clearScopes   = clearScopesReader @(Reducer m) @NExprLoc
  pushScopes    = pushScopesReader
  askLookupVar  = lookupVarReader
