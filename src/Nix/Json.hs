
module Nix.Json where

import qualified Data.Aeson                    as A
import qualified Data.Aeson.Encoding           as A
import qualified Data.HashMap.Lazy             as HM
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
import           Nix.Expr.Types

nvalueToJSONNixString :: MonadNix e t f m => NValue t f m -> m NixString
nvalueToJSONNixString =
  runWithStringContextT .
    fmap
      ( toStrict
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
  NVConstant NNull      -> pure   A.Null
  NVStr      ns         -> A.toJSON <$> extractNixString ns
  NVList l -> A.Array . V.fromList <$> traverse intoJson l
  NVSet _ m ->
    maybe
      (A.Object <$> traverse intoJson (HM.mapKeys (coerce @VarName @Text) m))
      intoJson
      (HM.lookup "outPath" m)
  NVPath p ->
    do
      fp <- lift $ coerce <$> addPath p
      addSingletonStringContext $ StringContext (fromString fp) DirectPath
      pure $ A.toJSON fp
  v -> lift $ throwError $ CoercionToJson v

 where
  intoJson :: MonadNix e t f m => NValue t f m -> WithStringContextT m A.Value
  intoJson nv = join $ lift $ nvalueToJSON <$> demand nv
