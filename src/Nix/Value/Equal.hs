{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}

module Nix.Value.Equal where

import           Control.Comonad
import           Control.Monad
import           Control.Monad.Free
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Data.Align
import           Data.Eq.Deriving
import           Data.Functor.Classes
import           Data.Functor.Identity
import qualified Data.HashMap.Lazy             as M
import           Data.These
import           Nix.Atoms
import           Nix.Frames
import           Nix.String
import           Nix.Thunk
import           Nix.Utils
import           Nix.Value

checkComparable
  :: (Framed e m, MonadDataErrorContext f m)
  => NValue f m
  -> NValue f m
  -> m ()
checkComparable x y = case (x, y) of
  (NVConstant (NFloat _), NVConstant (NInt _)) -> pure ()
  (NVConstant (NInt _), NVConstant (NFloat _)) -> pure ()
  (NVConstant (NInt _), NVConstant (NInt _)) -> pure ()
  (NVConstant (NFloat _), NVConstant (NFloat _)) -> pure ()
  (NVStr _, NVStr _) -> pure ()
  (NVPath _, NVPath _) -> pure ()
  _ -> throwError $ Comparison x y

-- | Checks whether two containers are equal, using the given item equality
--   predicate. If there are any item slots that don't match between the two
--   containers, the result will be False.
alignEqM
  :: (Align f, Traversable f, Monad m)
  => (a -> b -> m Bool)
  -> f a
  -> f b
  -> m Bool
alignEqM eq fa fb = fmap (either (const False) (const True)) $ runExceptT $ do
  pairs <- forM (Data.Align.align fa fb) $ \case
    These a b -> pure (a, b)
    _         -> throwE ()
  forM_ pairs $ \(a, b) -> guard =<< lift (eq a b)

alignEq :: (Align f, Traversable f) => (a -> b -> Bool) -> f a -> f b -> Bool
alignEq eq fa fb = runIdentity $ alignEqM (\x y -> Identity (eq x y)) fa fb

isDerivationM :: Monad m => (t -> m (Maybe NixString)) -> AttrSet t -> m Bool
isDerivationM f m = case M.lookup "type" m of
  Nothing -> pure False
  Just t  -> do
    mres <- f t
    case mres of
        -- We should probably really make sure the context is empty here
        -- but the C++ implementation ignores it.
      Just s  -> pure $ stringIgnoreContext s == "derivation"
      Nothing -> pure False

isDerivation :: Monad m => (t -> Maybe NixString) -> AttrSet t -> Bool
isDerivation f = runIdentity . isDerivationM (\x -> Identity (f x))

valueFEqM
  :: Monad n
  => (AttrSet a -> AttrSet a -> n Bool)
  -> (a -> a -> n Bool)
  -> NValueF p m a
  -> NValueF p m a
  -> n Bool
valueFEqM attrsEq eq = curry $ \case
  (NVConstantF (NFloat x), NVConstantF (NInt y)  ) -> pure $ x == fromInteger y
  (NVConstantF (NInt   x), NVConstantF (NFloat y)) -> pure $ fromInteger x == y
  (NVConstantF lc        , NVConstantF rc        ) -> pure $ lc == rc
  (NVStrF ls, NVStrF rs) ->
    pure $ stringIgnoreContext ls == stringIgnoreContext rs
  (NVListF ls , NVListF rs ) -> alignEqM eq ls rs
  (NVSetF lm _, NVSetF rm _) -> attrsEq lm rm
  (NVPathF lp , NVPathF rp ) -> pure $ lp == rp
  _                          -> pure False

valueFEq
  :: (AttrSet a -> AttrSet a -> Bool)
  -> (a -> a -> Bool)
  -> NValueF p m a
  -> NValueF p m a
  -> Bool
valueFEq attrsEq eq x y = runIdentity $ valueFEqM
  (\x' y' -> Identity (attrsEq x' y'))
  (\x' y' -> Identity (eq x' y'))
  x
  y

compareAttrSetsM
  :: Monad m
  => (t -> m (Maybe NixString))
  -> (t -> t -> m Bool)
  -> AttrSet t
  -> AttrSet t
  -> m Bool
compareAttrSetsM f eq lm rm = do
  isDerivationM f lm >>= \case
    True -> isDerivationM f rm >>= \case
      True
        | Just lp <- M.lookup "outPath" lm, Just rp <- M.lookup "outPath" rm -> eq
          lp
          rp
      _ -> compareAttrs
    _ -> compareAttrs
  where compareAttrs = alignEqM eq lm rm

compareAttrSets
  :: (t -> Maybe NixString)
  -> (t -> t -> Bool)
  -> AttrSet t
  -> AttrSet t
  -> Bool
compareAttrSets f eq lm rm = runIdentity
  $ compareAttrSetsM (\t -> Identity (f t)) (\x y -> Identity (eq x y)) lm rm

valueEqM
  :: forall t f m
   . (MonadThunk m, Thunk m ~ t, ThunkValue m ~ NValue f m, Comonad f)
  => NValue f m
  -> NValue f m
  -> m Bool
valueEqM (  Pure x) (  Pure y) = thunkEqM x y
valueEqM (  Pure x) y@(Free _) = thunkEqM x =<< thunk (pure y)
valueEqM x@(Free _) (  Pure y) = thunkEqM ?? y =<< thunk (pure x)
valueEqM (Free (NValue (extract -> x))) (Free (NValue (extract -> y))) =
  valueFEqM (compareAttrSetsM f valueEqM) valueEqM x y
 where
  f (Pure t) = force t $ \case
    NVStr s -> pure $ Just s
    _       -> pure Nothing
  f (Free v) = case v of
    NVStr' s -> pure $ Just s
    _        -> pure Nothing

thunkEqM :: (MonadThunk m, Thunk m ~ t, ThunkValue m ~ NValue f m, Comonad f) => t -> t -> m Bool
thunkEqM lt rt = force lt $ \lv -> force rt $ \rv ->
  let unsafePtrEq = case (lt, rt) of
        (lid, rid) | lid == rid -> pure True
        _ -> valueEqM lv rv
  in  case (lv, rv) of
        (NVClosure _ _, NVClosure _ _) -> unsafePtrEq
        (NVList _     , NVList _     ) -> unsafePtrEq
        (NVSet _ _    , NVSet _ _    ) -> unsafePtrEq
        _                              -> valueEqM lv rv

instance Eq1 (NValueF p m) where
  liftEq _  (NVConstantF x) (NVConstantF y) = x == y
  liftEq _  (NVStrF      x) (NVStrF      y) = x == y
  liftEq eq (NVListF     x) (NVListF     y) = liftEq eq x y
  liftEq eq (NVSetF x _   ) (NVSetF y _   ) = liftEq eq x y
  liftEq _  (NVPathF x    ) (NVPathF y    ) = x == y
  liftEq _  _               _               = False

$(deriveEq1 ''NValue')
