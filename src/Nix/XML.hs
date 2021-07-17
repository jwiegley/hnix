{-# LANGUAGE ScopedTypeVariables #-}

module Nix.XML
  ( toXML )
where

import qualified Data.HashMap.Lazy             as M
import           Nix.Atoms
import           Nix.Expr.Types
import           Nix.String
import           Nix.Value
import           Text.XML.Light                 ( Element(Element)
                                                , Attr(Attr)
                                                , Content(Elem)
                                                , unqual
                                                , ppElement
                                                )

toXML :: forall t f m . MonadDataContext f m => NValue t f m -> NixString
toXML = runWithStringContext . fmap pp . iterNValueByDiscardWith cyc phi
 where
  cyc = pure $ mkEVal "string" "<expr>"

  pp e =
    heading
    <> toText
        (ppElement $
          mkE
            "expr"
            [Elem e]
        )
    <> "\n"
   where
    heading = "<?xml version='1.0' encoding='utf-8'?>\n"

  phi :: NValue' t f m (WithStringContext Element) -> WithStringContext Element
  phi = \case
    NVConstant' a ->
      pure $
        case a of
          NURI   t -> mkEVal "string" $ toString t
          NInt   n -> mkEVal "int"    $ show n
          NFloat f -> mkEVal "float"  $ show f
          NBool  b -> mkEVal "bool"   $ if b then "true" else "false"
          NNull    -> mkE    "null"     mempty

    NVStr' str ->
      mkEVal "string" . toString <$> extractNixString str
    NVList' l ->
      do
        els <- sequence l
        pure $
          mkE
            "list"
            (Elem <$> els)

    NVSet' _ s ->
      do
        kvs <- sequence s
        pure $
          mkE
            "attrs"
            ((\ (k, v) ->
                Elem $
                  Element
                    (unqual "attr")
                    [Attr (unqual "name") (toString k)]
                    [Elem v]
                    Nothing
              ) <$>
                sortWith fst (M.toList kvs)
            )

    NVClosure' p _ ->
      pure $
        mkE
          "function"
          (paramsXML p)
    NVPath' fp        -> pure $ mkEVal "path" fp
    NVBuiltin' name _ -> pure $ mkEName "function" $ toString name

mkE :: String -> [Content] -> Element
mkE n c =
  Element
    (unqual n)
    mempty
    c
    Nothing

mkElem :: String -> String -> String -> Element
mkElem n a v =
  Element
    (unqual n)
    [Attr (unqual a) v]
    mempty
    Nothing

mkEVal :: String -> String -> Element
mkEVal = (`mkElem` "value")

mkEName :: String -> String -> Element
mkEName = (`mkElem` "name")

paramsXML :: Params r -> [Content]
paramsXML (Param name) = [Elem $ mkEName "varpat" (toString name)]
paramsXML (ParamSet s b mname) =
  [Elem $ Element (unqual "attrspat") (battr <> nattr) (paramSetXML s) Nothing]
 where
  battr = [ Attr (unqual "ellipsis") "1" | b ]
  nattr =
    maybe
      mempty
      ((: mempty) . Attr (unqual "name") . toString)
      mname

paramSetXML :: ParamSet r -> [Content]
paramSetXML = fmap (\(k, _) -> Elem $ mkEName "attr" (toString k))
