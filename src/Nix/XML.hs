{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Nix.XML (toXML) where

import qualified Data.HashMap.Lazy             as M
import           Data.List
import           Data.Ord
import qualified Data.Text                     as Text
import           Nix.Atoms
import           Nix.Expr.Types
import           Nix.String
import           Nix.Value
import           Text.XML.Light

toXML :: forall f m . MonadDataContext f m => NValue f m -> NixString
toXML = runWithStringContext . fmap pp . iterNValue (\_ _ -> cyc) phi
 where
  cyc = pure $ mkElem "string" "value" "<expr>"

  pp =
    ("<?xml version='1.0' encoding='utf-8'?>\n" <>)
      . (<> "\n")
      . Text.pack
      . ppElement
      . (\e -> Element (unqual "expr") [] [Elem e] Nothing)

  phi :: NValue' f m (WithStringContext Element) -> WithStringContext Element
  phi = \case
    NVConstant' a -> case a of
      NURI   t -> pure $ mkElem "string" "value" (Text.unpack t)
      NInt   n -> pure $ mkElem "int" "value" (show n)
      NFloat f -> pure $ mkElem "float" "value" (show f)
      NBool  b -> pure $ mkElem "bool" "value" (if b then "true" else "false")
      NNull    -> pure $ Element (unqual "null") [] [] Nothing

    NVStr' str ->
      mkElem "string" "value" . Text.unpack <$> extractNixString str
    NVList' l -> sequence l
      >>= \els -> pure $ Element (unqual "list") [] (Elem <$> els) Nothing

    NVSet' s _ -> sequence s >>= \kvs -> pure $ Element
      (unqual "attrs")
      []
      (map
        (\(k, v) -> Elem
          (Element (unqual "attr")
                   [Attr (unqual "name") (Text.unpack k)]
                   [Elem v]
                   Nothing
          )
        )
        (sortBy (comparing fst) $ M.toList kvs)
      )
      Nothing

    NVClosure' p _ ->
      pure $ Element (unqual "function") [] (paramsXML p) Nothing
    NVPath' fp        -> pure $ mkElem "path" "value" fp
    NVBuiltin' name _ -> pure $ mkElem "function" "name" name
    _                 -> error "Pattern synonyms mask coverage"

mkElem :: String -> String -> String -> Element
mkElem n a v = Element (unqual n) [Attr (unqual a) v] [] Nothing

paramsXML :: Params r -> [Content]
paramsXML (Param name) = [Elem $ mkElem "varpat" "name" (Text.unpack name)]
paramsXML (ParamSet s b mname) =
  [Elem $ Element (unqual "attrspat") (battr <> nattr) (paramSetXML s) Nothing]
 where
  battr = [ Attr (unqual "ellipsis") "1" | b ]
  nattr = maybe [] ((: []) . Attr (unqual "name") . Text.unpack) mname

paramSetXML :: ParamSet r -> [Content]
paramSetXML = fmap (\(k, _) -> Elem $ mkElem "attr" "name" (Text.unpack k))
