{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}


-- | Code for rendering/representation of the messages packaged with their context (Frames).
module Nix.Render.Frame where

import           Control.Monad.Reader
import           Data.Fix
import           Data.Typeable
import           Nix.Eval
import           Nix.Exec
import           Nix.Expr
import           Nix.Frames
import           Nix.Normal
import           Nix.Options
import           Nix.Pretty
import           Nix.Render
import           Nix.Thunk
import           Nix.Utils
import           Nix.Value
import           Prettyprinter
import           Text.Megaparsec.Pos
#ifdef MIN_VERSION_pretty_show
import qualified Text.Show.Pretty as PS
#endif

renderFrames
  :: forall v t f e m ann
   . ( MonadReader e m
     , Has e Options
     , MonadFile m
     , MonadCitedThunks t f m
     , Typeable v
     )
  => Frames
  -> m (Doc ann)
renderFrames []       = pure mempty
renderFrames (x : xs) = do
  opts :: Options <- asks (view hasLens)
  frames          <- if
    | verbose opts <= ErrorsOnly -> renderFrame @v @t @f x
    | verbose opts <= Informational -> do
      f <- renderFrame @v @t @f x
      pure $ concatMap go (reverse xs) <> f
    | otherwise -> concat <$> mapM (renderFrame @v @t @f) (reverse (x : xs))
  pure $ case frames of
    [] -> mempty
    _  -> vsep frames
 where
  go :: NixFrame -> [Doc ann]
  go f = case framePos @v @m f of
    Just pos ->
      ["While evaluating at " <> pretty (sourcePosPretty pos) <> colon]
    Nothing -> []

framePos
  :: forall v (m :: * -> *)
   . (Typeable m, Typeable v)
  => NixFrame
  -> Maybe SourcePos
framePos (NixFrame _ f)
  | Just (e :: EvalFrame m v) <- fromException f = case e of
    EvaluatingExpr _ (Fix (Compose (Ann (SrcSpan beg _) _))) -> Just beg
    _ -> Nothing
  | otherwise = Nothing

renderFrame
  :: forall v t f e m ann
   . ( MonadReader e m
     , Has e Options
     , MonadFile m
     , MonadCitedThunks t f m
     , Typeable v
     )
  => NixFrame
  -> m [Doc ann]
renderFrame (NixFrame level f)
  | Just (e :: EvalFrame m v) <- fromException f = renderEvalFrame level e
  | Just (e :: ThunkLoop) <- fromException f = renderThunkLoop level e
  | Just (e :: ValueFrame f m) <- fromException f = renderValueFrame level e
  | Just (e :: NormalLoop f m) <- fromException f = renderNormalLoop level e
  | Just (e :: ExecFrame f m) <- fromException f = renderExecFrame level e
  | Just (e :: ErrorCall) <- fromException f = pure [pretty (show e)]
  | Just (e :: SynHoleInfo m v) <- fromException f = pure [pretty (show e)]
  | otherwise = error $ "Unrecognized frame: " <> show f

wrapExpr :: NExprF r -> NExpr
wrapExpr x = Fix (Fix (NSym "<?>") <$ x)

renderEvalFrame
  :: (MonadReader e m, Has e Options, MonadFile m)
  => NixLevel
  -> EvalFrame m v
  -> m [Doc ann]
renderEvalFrame level f = do
  opts :: Options <- asks (view hasLens)
  case f of
    EvaluatingExpr scope e@(Fix (Compose (Ann ann _))) -> do
      let scopeInfo | showScopes opts = [pretty $ show scope]
                    | otherwise   = []
      fmap (\x -> scopeInfo <> [x])
        $   renderLocation ann
        =<< renderExpr level "While evaluating" "Expression" e

    ForcingExpr _scope e@(Fix (Compose (Ann ann _))) | thunks opts ->
      fmap (: [])
        $   renderLocation ann
        =<< renderExpr level "While forcing thunk from" "Forcing thunk" e

    Calling name ann ->
      fmap (: [])
        $  renderLocation ann
        $  "While calling builtins."
        <> pretty name

    SynHole synfo ->
      sequence
        $ let e@(Fix (Compose (Ann ann _))) = _synHoleInfo_expr synfo
          in  [ renderLocation ann
                =<< renderExpr level "While evaluating" "Syntactic Hole" e
              , pure $ pretty $ show (_synHoleInfo_scope synfo)
              ]

    ForcingExpr _ _ -> pure []


renderExpr
  :: (MonadReader e m, Has e Options, MonadFile m)
  => NixLevel
  -> String
  -> String
  -> NExprLoc
  -> m (Doc ann)
renderExpr _level longLabel shortLabel e@(Fix (Compose (Ann _ x))) = do
  opts :: Options <- asks (view hasLens)
  let rendered
          | verbose opts >= DebugInfo =
#ifdef MIN_VERSION_pretty_show
              pretty (PS.ppShow (stripAnnotation e))
#else
              pretty (show (stripAnnotation e))
#endif
          | verbose opts >= Chatty = prettyNix (stripAnnotation e)
          | otherwise = prettyNix (Fix (Fix (NSym "<?>") <$ x))
  pure $ if verbose opts >= Chatty
    then
      vsep [pretty (longLabel <> ":\n>>>>>>>>"), indent 2 rendered, "<<<<<<<<"]
    else pretty shortLabel <> fillSep [": ", rendered]

renderValueFrame
  :: forall e t f m ann
   . (MonadReader e m, Has e Options, MonadFile m, MonadCitedThunks t f m)
  => NixLevel
  -> ValueFrame f m
  -> m [Doc ann]
renderValueFrame level = fmap (: []) . \case
  ForcingThunk    _t -> pure "ForcingThunk" -- jww (2019-03-18): NYI
  ConcerningValue _v -> pure "ConcerningValue"
  Comparison     _ _ -> pure "Comparing"
  Addition       _ _ -> pure "Adding"
  Division       _ _ -> pure "Dividing"
  Multiplication _ _ -> pure "Multiplying"

  Coercion       x y -> pure
    $ mconcat [desc, pretty (describeValue x), " to ", pretty (describeValue y)]
   where
    desc | level <= Error = "Cannot coerce "
         | otherwise      = "While coercing "

  CoercionToJson v -> do
    v' <- renderValue level "" "" v
    pure $ "CoercionToJson " <> v'
  CoercionFromJson _j -> pure "CoercionFromJson"
  Expectation t v     -> do
    v' <- renderValue @_ @t @f @m level "" "" v
    pure $ "Saw " <> v' <> " but expected " <> pretty (describeValue t)

renderValue
  :: forall e t f m ann
   . (MonadReader e m, Has e Options, MonadFile m, MonadCitedThunks t f m)
  => NixLevel
  -> String
  -> String
  -> NValue f m
  -> m (Doc ann)
renderValue _level _longLabel _shortLabel v = do
  opts :: Options <- asks (view hasLens)
  (if values opts
     then prettyNValueProv
     else prettyNValue) <$> removeEffects v

renderExecFrame
  :: (MonadReader e m, Has e Options, MonadFile m, MonadCitedThunks t f m)
  => NixLevel
  -> ExecFrame f m
  -> m [Doc ann]
renderExecFrame level = \case
  Assertion ann v ->
    fmap (: [])
      $   renderLocation ann
      =<< (   (\d -> fillSep ["Assertion failed:", d])
          <$> renderValue level "" "" v
          )

renderThunkLoop
  :: (MonadReader e m, Has e Options, MonadFile m, Show (Thunk m))
  => NixLevel
  -> ThunkLoop
  -> m [Doc ann]
renderThunkLoop _level = pure . (: []) . \case
  ThunkLoop n -> pretty $ "Infinite recursion in thunk " <> n

renderNormalLoop
  :: (MonadReader e m, Has e Options, MonadFile m, MonadCitedThunks t f m)
  => NixLevel
  -> NormalLoop f m
  -> m [Doc ann]
renderNormalLoop level = fmap (: []) . \case
  NormalLoop v -> do
    v' <- renderValue level "" "" v
    pure $ "Infinite recursion during normalization forcing " <> v'
