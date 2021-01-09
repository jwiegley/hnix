{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Nix.Json where

import           Control.Arrow                  ( first )
import           Control.Monad
import           Control.Monad.Trans
import qualified Data.Aeson                    as A
import qualified Data.Aeson.Encoding           as A
import qualified Data.HashMap.Lazy             as HM
import           Data.Interned
import qualified Data.Text                     as Text
import qualified Data.Text.Lazy                as TL
import qualified Data.Text.Lazy.Encoding       as TL
import qualified Data.Vector                   as V
import           Nix.Atoms
import           Nix.Effects
import           Nix.Exec
import           Nix.Frames
import           Nix.String
import           Nix.Utils
import           Nix.Value
import           Nix.Value.Monad

nvalueToJSONNixString :: MonadNix e t f m => NValue t f m -> m NixString
nvalueToJSONNixString =
  runWithStringContextT
    . fmap
        ( TL.toStrict
        . TL.decodeUtf8
        . A.encodingToLazyByteString
        . toEncodingSorted
        )
    . nvalueToJSON

nvalueToJSON :: MonadNix e t f m => NValue t f m -> WithStringContextT m A.Value
nvalueToJSON = \case
  NVConstant (NInt   n) -> pure $ A.toJSON n
  NVConstant (NFloat n) -> pure $ A.toJSON n
  NVConstant (NBool  b) -> pure $ A.toJSON b
  NVConstant NNull      -> pure $ A.Null
  NVStr      ns         -> A.toJSON <$> extractNixString ns
  NVList l ->
    A.Array
      .   V.fromList
      <$> traverse (join . lift . flip demand (pure . nvalueToJSON)) l
  NVSet m _ -> case HM.lookup "outPath" m of
    Nothing ->
      A.Object . HM.fromList . map (first unintern) . HM.toList
        <$> traverse (join . lift . flip demand (pure . nvalueToJSON)) m
    Just outPath -> join $ lift $ demand outPath (pure . nvalueToJSON)
  NVPath p -> do
    fp <- lift $ unStorePath <$> addPath p
    addSingletonStringContext $ StringContext (Text.pack fp) DirectPath
    pure $ A.toJSON fp
  v -> lift $ throwError $ CoercionToJson v
