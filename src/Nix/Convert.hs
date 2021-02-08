{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- | Although there are a lot of instances in this file, really it's just a
--   combinatorial explosion of the following combinations:
--
--   - Several Haskell types being converted to/from Nix wrappers
--   - Several types of Nix wrappers
--   - Whether to be shallow or deep while unwrapping

module Nix.Convert where

import           Control.Monad.Free
import           Data.ByteString
import qualified Data.HashMap.Lazy             as M
import           Data.Maybe
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import           Data.Text.Encoding             ( encodeUtf8
                                                , decodeUtf8
                                                )
import           Nix.Atoms
import           Nix.Effects
import           Nix.Expr.Types
import           Nix.Expr.Types.Annotated
import           Nix.Frames
import           Nix.String
import           Nix.Value
import           Nix.Value.Monad
import           Nix.Thunk
import           Nix.Utils

newtype Deeper a = Deeper { getDeeper :: a }
  deriving (Typeable, Functor, Foldable, Traversable)

{-

IMPORTANT NOTE

We used to have Text instances of FromValue, ToValue, FromNix, and ToNix.
However, we're removing these instances because they are dangerous due to the
fact that they hide the way string contexts are handled. It's better to have to
explicitly handle string context in a way that is appropriate for the situation.

Do not add these instances back!

-}

---------------------------------------------------------------------------------
-- * FromValue
---------------------------------------------------------------------------------

class FromValue a m v where
    fromValue    :: v -> m a
    fromValueMay :: v -> m (Maybe a)

type Convertible e t f m
  = (Framed e m, MonadDataErrorContext f m, MonadThunk m, Thunk m ~ t, ThunkValue m ~ NValue f m)

instance ( Convertible e t f m
         , MonadValue (NValue f m) m
         , FromValue a m (NValue' f m (NValue f m))
         )
  => FromValue a m (Free (NValue' f m) t) where
  fromValueMay = flip demand $ \case
    Pure t -> force t fromValueMay
    Free v -> fromValueMay v
  fromValue = flip demand $ \case
    Pure t -> force t fromValue
    Free v -> fromValue v

instance ( Convertible e t f m
         , MonadValue (NValue f m) m
         , FromValue a m (Deeper (NValue' f m (NValue f m)))
         )
  => FromValue a m (Deeper (Free (NValue' f m) t)) where
  fromValueMay (Deeper v) = demand v $ \case
    Pure t -> force t (fromValueMay . Deeper)
    Free v -> fromValueMay (Deeper v)
  fromValue (Deeper v) = demand v $ \case
    Pure t -> force t (fromValue . Deeper)
    Free v -> fromValue (Deeper v)

instance Convertible e t f m
  => FromValue () m (NValue' f m (Free (NValue' f m) t)) where
  fromValueMay = \case
    NVConstant' NNull -> pure $ Just ()
    _                 -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m TNull (Free v)

instance Convertible e t f m
  => FromValue Bool m (NValue' f m (Free (NValue' f m) t)) where
  fromValueMay = \case
    NVConstant' (NBool b) -> pure $ Just b
    _                     -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m TBool (Free v)

instance Convertible e t f m
  => FromValue Int m (NValue' f m (Free (NValue' f m) t)) where
  fromValueMay = \case
    NVConstant' (NInt b) -> pure $ Just (fromInteger b)
    _                    -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m TInt (Free v)

instance Convertible e t f m
  => FromValue Integer m (NValue' f m (Free (NValue' f m) t)) where
  fromValueMay = \case
    NVConstant' (NInt b) -> pure $ Just b
    _                    -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m TInt (Free v)

instance Convertible e t f m
  => FromValue Float m (NValue' f m (Free (NValue' f m) t)) where
  fromValueMay = \case
    NVConstant' (NFloat b) -> pure $ Just b
    NVConstant' (NInt   i) -> pure $ Just (fromInteger i)
    _                      -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m TFloat (Free v)

instance ( Convertible e t f m
         , MonadValue (NValue f m) m
         , MonadEffects f m
         )
  => FromValue NixString m (NValue' f m (Free (NValue' f m) t)) where
  fromValueMay = \case
    NVStr' ns -> pure $ Just ns
    NVPath' p ->
      Just
        .   (\s -> makeNixStringWithSingletonContext s (StringContext s DirectPath))
        .   Text.pack
        .   unStorePath
        <$> addPath p
    NVSet' s _ -> case M.lookup "outPath" s of
      Nothing -> pure Nothing
      Just p  -> fromValueMay p
    _ -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m (TString NoContext) (Free v)

instance Convertible e t f m
  => FromValue ByteString m (NValue' f m (Free (NValue' f m) t)) where
  fromValueMay = \case
    NVStr' ns -> pure $ encodeUtf8 <$> getStringNoContext  ns
    _         -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m (TString NoContext) (Free v)

newtype Path = Path { getPath :: FilePath }
    deriving Show

instance ( Convertible e t f m
         , MonadValue (NValue f m) m
         )
  => FromValue Path m (NValue' f m (Free (NValue' f m) t)) where
  fromValueMay = \case
    NVPath' p  -> pure $ Just (Path p)
    NVStr'  ns -> pure $ Path . Text.unpack <$> getStringNoContext  ns
    NVSet' s _ -> case M.lookup "outPath" s of
      Nothing -> pure Nothing
      Just p  -> fromValueMay @Path p
    _ -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m TPath (Free v)

instance Convertible e t f m
  => FromValue [Free (NValue' f m) t] m (NValue' f m (Free (NValue' f m) t)) where
  fromValueMay = \case
    NVList' l -> pure $ Just l
    _         -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m TList (Free v)

instance ( Convertible e t f m
         , FromValue a m (NValue f m)
         )
  => FromValue [a] m (Deeper (NValue' f m (Free (NValue' f m) t))) where
  fromValueMay = \case
    Deeper (NVList' l) -> sequence <$> traverse fromValueMay l
    _                  -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m TList (Free (getDeeper v))

instance Convertible e t f m
  => FromValue (AttrSet (Free (NValue' f m) t)) m (NValue' f m (Free (NValue' f m) t)) where
  fromValueMay = \case
    NVSet' s _ -> pure $ Just s
    _          -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m TSet (Free v)

instance ( Convertible e t f m
         , FromValue a m (NValue f m)
         )
  => FromValue (AttrSet a) m (Deeper (NValue' f m (Free (NValue' f m) t))) where
  fromValueMay = \case
    Deeper (NVSet' s _) -> sequence <$> traverse fromValueMay s
    _                   -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m TSet (Free (getDeeper v))

instance Convertible e t f m
  => FromValue (AttrSet (Free (NValue' f m) t), AttrSet SourcePos) m
              (NValue' f m (Free (NValue' f m) t)) where
  fromValueMay = \case
    NVSet' s p -> pure $ Just (s, p)
    _          -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m TSet (Free v)

instance ( Convertible e t f m
         , FromValue a m (NValue f m)
         )
  => FromValue (AttrSet a, AttrSet SourcePos) m
              (Deeper (NValue' f m (Free (NValue' f m) t))) where
  fromValueMay = \case
    Deeper (NVSet' s p) -> fmap (, p) . sequence <$> traverse fromValueMay s
    _                   -> pure Nothing
  fromValue v = fromValueMay v >>= \case
    Just b -> pure b
    _      -> throwError $ Expectation @f @m TSet (Free (getDeeper v))

-- This instance needs IncoherentInstances, and only because of ToBuiltin
instance ( Convertible e t f m
         , FromValue a m (NValue' f m (NValue f m))
         )
  => FromValue a m (Deeper (NValue' f m (Free (NValue' f m) t))) where
  fromValueMay = fromValueMay . getDeeper
  fromValue    = fromValue . getDeeper

---------------------------------------------------------------------------------
-- * ToValue
---------------------------------------------------------------------------------

class ToValue a m v where
    toValue :: a -> m v

instance (Convertible e t f m, ToValue a m (NValue' f m (NValue f m)))
  => ToValue a m (Free (NValue' f m) t) where
  toValue = fmap Free . toValue

instance ( Convertible e t f m
         , ToValue a m (Deeper (NValue' f m (NValue f m)))
         )
  => ToValue a m (Deeper (Free (NValue' f m) t)) where
  toValue = fmap (fmap Free) . toValue

instance Convertible e t f m
  => ToValue () m (NValue' f m (Free (NValue' f m) t)) where
  toValue _ = pure . nvConstant' $ NNull

instance Convertible e t f m
  => ToValue Bool m (NValue' f m (Free (NValue' f m) t)) where
  toValue = pure . nvConstant' . NBool

instance Convertible e t f m
  => ToValue Int m (NValue' f m (Free (NValue' f m) t)) where
  toValue = pure . nvConstant' . NInt . toInteger

instance Convertible e t f m
  => ToValue Integer m (NValue' f m (Free (NValue' f m) t)) where
  toValue = pure . nvConstant' . NInt

instance Convertible e t f m
  => ToValue Float m (NValue' f m (Free (NValue' f m) t)) where
  toValue = pure . nvConstant' . NFloat

instance Convertible e t f m
  => ToValue NixString m (NValue' f m (Free (NValue' f m) t)) where
  toValue = pure . nvStr'

instance Convertible e t f m
  => ToValue ByteString m (NValue' f m (Free (NValue' f m) t)) where
  toValue = pure . nvStr' . makeNixStringWithoutContext . decodeUtf8

instance Convertible e t f m
  => ToValue Path m (NValue' f m (Free (NValue' f m) t)) where
  toValue = pure . nvPath' . getPath

instance Convertible e t f m
  => ToValue StorePath m (NValue' f m (Free (NValue' f m) t)) where
  toValue = toValue . Path . unStorePath

instance ( Convertible e t f m
         )
  => ToValue SourcePos m (NValue' f m (Free (NValue' f m) t)) where
  toValue (SourcePos f l c) = do
    f' <- toValue (makeNixStringWithoutContext (Text.pack f))
    l' <- toValue (unPos l)
    c' <- toValue (unPos c)
    let pos = M.fromList [("file" :: Text, f'), ("line", l'), ("column", c')]
    pure $ nvSet' pos mempty

-- | With 'ToValue', we can always act recursively
instance Convertible e t f m
  => ToValue [Free (NValue' f m) t] m (NValue' f m (Free (NValue' f m) t)) where
  toValue = pure . nvList'

instance (Convertible e t f m, ToValue a m (NValue f m))
  => ToValue [a] m (Deeper (NValue' f m (Free (NValue' f m) t))) where
  toValue = fmap (Deeper . nvList') . traverse toValue

instance Convertible e t f m
  => ToValue (AttrSet (Free (NValue' f m) t)) m (NValue' f m (Free (NValue' f m) t)) where
  toValue s = pure $ nvSet' s mempty

instance (Convertible e t f m, ToValue a m (NValue f m))
  => ToValue (AttrSet a) m (Deeper (NValue' f m (Free (NValue' f m) t))) where
  toValue s = (Deeper .) . nvSet' <$> traverse toValue s <*> pure mempty

instance Convertible e t f m
  => ToValue (AttrSet (Free (NValue' f m) t), AttrSet SourcePos) m
            (NValue' f m (Free (NValue' f m) t)) where
  toValue (s, p) = pure $ nvSet' s p

instance (Convertible e t f m, ToValue a m (NValue f m))
  => ToValue (AttrSet a, AttrSet SourcePos) m
            (Deeper (NValue' f m (Free (NValue' f m) t))) where
  toValue (s, p) = (Deeper .) . nvSet' <$> traverse toValue s <*> pure p

instance Convertible e t f m
  => ToValue NixLikeContextValue m (NValue' f m (Free (NValue' f m) t)) where
  toValue nlcv = do
    path <- if nlcvPath nlcv then Just <$> toValue True else pure Nothing
    allOutputs <- if nlcvAllOutputs nlcv
      then Just <$> toValue True
      else pure Nothing
    outputs <- do
      let outputs =
            makeNixStringWithoutContext <$> nlcvOutputs nlcv
      ts :: [NValue f m] <- traverse toValue outputs
      case ts of
        [] -> pure Nothing
        _  -> Just <$> toValue ts
    pure $ flip nvSet' M.empty $ M.fromList $ catMaybes
      [ ("path",) <$> path
      , ("allOutputs",) <$> allOutputs
      , ("outputs",) <$> outputs
      ]

instance Convertible e t f m => ToValue () m (NExprF (Free (NValue' f m) t)) where
  toValue _ = pure . NConstant $ NNull

instance Convertible e t f m => ToValue Bool m (NExprF (Free (NValue' f m) t)) where
  toValue = pure . NConstant . NBool
