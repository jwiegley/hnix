{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- | Main module for parsing Nix expressions.
module Nix.Parser
  ( parseNixFile
  , parseNixFileLoc
  , parseNixText
  , parseNixTextLoc
  , parseFromFileEx
  , Parser
  , parseFromText
  , Result
  , reservedNames
  , OperatorInfo(..)
  , NSpecialOp(..)
  , NAssoc(..)
  , NOperatorDef
  , getUnaryOperator
  , getBinaryOperator
  , getSpecialOperator
  , nixToplevelForm
  , nixExpr
  , nixSet
  , nixBinders
  , nixSelector
  , nixSym
  , nixPath
  , nixString
  , nixUri
  , nixSearchPath
  , nixFloat
  , nixInt
  , nixBool
  , nixNull
  , symbol
  , whiteSpace
  )
where

import           Prelude                 hiding ( some
                                                , many
                                                , readFile
                                                )
import           Data.Foldable                  ( foldr1 )

import           Control.Monad                  ( msum )
import           Control.Monad.Combinators.Expr ( makeExprParser
                                                , Operator( Postfix
                                                          , InfixN
                                                          , InfixR
                                                          , Prefix
                                                          , InfixL
                                                          )
                                                )
import           Data.Char                      ( isAlpha
                                                , isDigit
                                                , isSpace
                                                )
import           Data.Data                      ( Data(..) )
import           Data.Fix                       ( Fix(..) )
import qualified Data.HashSet                  as HashSet
import qualified Data.Map                      as Map
import           Data.Text                      ( cons )
import           Nix.Expr                hiding ( ($>) )
import           Nix.Expr.Strings               ( escapeCodes
                                                , stripIndent
                                                , mergePlain
                                                , removePlainEmpty
                                                )
import           Nix.Render                     ( MonadFile(readFile) )
import           Prettyprinter                  ( Doc
                                                , pretty
                                                )
-- `parser-combinators` ships performance enhanced & MonadPlus-aware combinators.
-- For example `smome` and `many` impoted here.
import           Text.Megaparsec         hiding ( State )
import           Text.Megaparsec.Char           ( space1
                                                , string
                                                , letterChar
                                                , char
                                                )
import qualified Text.Megaparsec.Char.Lexer    as Lexer

-- | Different to @isAlphaNum@
isAlphanumeric :: Char -> Bool
isAlphanumeric x = isAlpha x || isDigit x
{-# inline isAlphanumeric #-}

infixl 3 <+>
(<+>) :: MonadPlus m => m a -> m a -> m a
(<+>) = mplus

---------------------------------------------------------------------------------

nixExpr :: Parser NExprLoc
nixExpr =
  makeExprParser
    nixTerm $
      snd <<$>>
        nixOperators nixSelector

antiStart :: Parser Text
antiStart = symbol "${" <?> "${"

nixAntiquoted :: Parser a -> Parser (Antiquoted a NExprLoc)
nixAntiquoted p =
  Antiquoted <$>
    (antiStart *> nixToplevelForm <* symbol "}")
      <+> Plain <$>
        p
      <?> "anti-quotation"

selDot :: Parser ()
selDot = try (symbol "." *> notFollowedBy nixPath) <?> "."

nixSelect :: Parser NExprLoc -> Parser NExprLoc
nixSelect term =
  do
    res <-
      liftA2 build
        term
        (optional $
          liftA2 (,)
            (selDot *> nixSelector)
            (optional $ reserved "or" *> nixTerm)
        )
    continues <- optional $ lookAhead selDot

    maybe
      id
      (const nixSelect)
      continues
      (pure res)
 where
  build
    :: NExprLoc
    -> Maybe ( Ann SrcSpan (NAttrPath NExprLoc)
        , Maybe NExprLoc
        )
    -> NExprLoc
  build t mexpr =
    maybe
      t
      (\ (a, m) -> (`nSelectLoc` t) m a)
      mexpr

nixSelector :: Parser (Ann SrcSpan (NAttrPath NExprLoc))
nixSelector =
  annotateLocation $
    do
      (x : xs) <- keyName `sepBy1` selDot
      pure $ x :| xs

nixTerm :: Parser NExprLoc
nixTerm = do
  c <- try $ lookAhead $ satisfy $ \x ->
    pathChar x || (`elem` ("({[</\"'^" :: String)) x
  case c of
    '('  -> nixSelect nixParens
    '{'  -> nixSelect nixSet
    '['  -> nixList
    '<'  -> nixSearchPath
    '/'  -> nixPath
    '"'  -> nixString
    '\'' -> nixString
    '^'  -> nixSynHole
    _ ->
      msum
        $  [ nixSelect nixSet | c == 'r' ]
        <> [ nixPath | pathChar c ]
        <> if isDigit c
             then [ nixFloat, nixInt ]
             else
               [ nixUri | isAlpha c ]
               <> [ nixBool | c == 't' || c == 'f' ]
               <> [ nixNull | c == 'n' ]
               <> [ nixSelect nixSym ]

nixToplevelForm :: Parser NExprLoc
nixToplevelForm = keywords <+> nixLambda <+> nixExpr
 where
  keywords = nixLet <+> nixIf <+> nixAssert <+> nixWith

nixSym :: Parser NExprLoc
nixSym = annotateLocation1 $ mkSymF . coerce <$> identifier

nixSynHole :: Parser NExprLoc
nixSynHole = annotateLocation1 $ mkSynHoleF . coerce <$> (char '^' *> identifier)

nixInt :: Parser NExprLoc
nixInt = annotateLocation1 (mkIntF <$> integer <?> "integer")

nixFloat :: Parser NExprLoc
nixFloat =
  annotateLocation1 (try (mkFloatF . realToFrac <$> float) <?> "float")

nixBool :: Parser NExprLoc
nixBool =
  annotateLocation1 (bool "true" True <+> bool "false" False) <?> "bool"
 where
  bool str b = mkBoolF b <$ reserved str

nixNull :: Parser NExprLoc
nixNull = annotateLocation1 (mkNullF <$ reserved "null" <?> "null")

-- | 'nixTopLevelForm' returns an expression annotated with a source position,
-- however this position doesn't include the parsed parentheses, so remove the
-- "inner" location annotateion and annotate again, including the parentheses.
nixParens :: Parser NExprLoc
nixParens = annotateLocation1 (parens (stripAnn . unFix <$> nixToplevelForm) <?> "parens")

nixList :: Parser NExprLoc
nixList = annotateLocation1 (brackets (NList <$> many nixTerm) <?> "list")

pathChar :: Char -> Bool
pathChar x =
  isAlphanumeric x || (`elem` ("._-+~" :: String)) x

slash :: Parser Char
slash =
  try
    (  char '/'
    <* notFollowedBy (satisfy (\x -> x == '/' || x == '*' || isSpace x))
    )
    <?> "slash"

-- | A path surrounded by angle brackets, indicating that it should be
-- looked up in the NIX_PATH environment variable at evaluation.
nixSearchPath :: Parser NExprLoc
nixSearchPath =
  annotateLocation1
    (mkPathF True <$>
      try (char '<' *> many (satisfy pathChar <+> slash) <* symbol ">")
      <?> "spath"
    )

pathStr :: Parser FilePath
pathStr =
  lexeme $
    liftA2 (<>)
      (many $ satisfy pathChar)
      (concat <$>
        some
          (liftA2 (:)
            slash
            (some $ satisfy pathChar)
          )
      )

nixPath :: Parser NExprLoc
nixPath = annotateLocation1 (try (mkPathF False <$> pathStr) <?> "path")

nixLet :: Parser NExprLoc
nixLet = annotateLocation1
  (reserved "let" *> (letBody <+> letBinders) <?> "let block")
 where
  letBinders =
    liftA2 NLet
      nixBinders
      (reserved "in" *> nixToplevelForm)
  -- Let expressions `let {..., body = ...}' are just desugared
  -- into `(rec {..., body = ...}).body'.
  letBody    = (\x -> NSelect Nothing x (StaticKey "body" :| mempty)) <$> aset
  aset       = annotateLocation1 $ NSet Recursive <$> braces nixBinders

nixIf :: Parser NExprLoc
nixIf = annotateLocation1
  (liftA3 NIf
    (reserved "if"   *> nixExpr        )
    (reserved "then" *> nixToplevelForm)
    (reserved "else" *> nixToplevelForm)
  <?> "if"
  )

nixAssert :: Parser NExprLoc
nixAssert = annotateLocation1
  (liftA2 NAssert
    (reserved "assert" *> nixToplevelForm)
    (semi              *> nixToplevelForm)
  <?> "assert"
  )

nixWith :: Parser NExprLoc
nixWith = annotateLocation1
  (liftA2 NWith
    (reserved "with" *> nixToplevelForm)
    (semi            *> nixToplevelForm)
  <?> "with"
  )

nixLambda :: Parser NExprLoc
nixLambda =
  liftA2 nAbs
    (annotateLocation $ try argExpr)
    nixToplevelForm

nixString :: Parser NExprLoc
nixString = nStr <$> annotateLocation nixString'

nixUri :: Parser NExprLoc
nixUri = lexeme $ annotateLocation1 $ try $ do
  start    <- letterChar
  protocol <- many $
    satisfy $
      \ x ->
        isAlphanumeric x
        || (`elem` ("+-." :: String)) x
  _       <- string ":"
  address <-
    some $
      satisfy $
        \ x ->
          isAlphanumeric x
          || (`elem` ("%/?:@&=+$,-_.!~*'" :: String)) x
  pure $ NStr $ DoubleQuoted
    [Plain $ toText $ start : protocol ++ ':' : address]

nixString' :: Parser (NString NExprLoc)
nixString' = lexeme (doubleQuoted <+> indented <?> "string")
 where
  doubleQuoted :: Parser (NString NExprLoc)
  doubleQuoted =
    DoubleQuoted
    . removePlainEmpty
    . mergePlain <$>
      ( doubleQ
      *> many (stringChar doubleQ (void $ char '\\') doubleEscape)
      <* doubleQ
      )
      <?> "double quoted string"

  doubleQ      = void $ char '"'
  doubleEscape = Plain . one <$> (char '\\' *> escapeCode)

  indented :: Parser (NString NExprLoc)
  indented =
    stripIndent <$>
      (indentedQ
      *> many (stringChar indentedQ indentedQ indentedEscape)
      <* indentedQ
      )
      <?> "indented string"

  indentedQ      = void (string "''" <?> "\"''\"")
  indentedEscape =
    try $
      do
        indentedQ
        (Plain <$> ("''" <$ char '\'' <+> "$" <$ char '$')) <+>
          do
            _ <- char '\\'
            c <- escapeCode

            pure $
              bool
                EscapedNewline
                (Plain $ one c)
                (c /= '\n')

  stringChar end escStart esc =
    Antiquoted <$>
      (antiStart *> nixToplevelForm <* char '}')
        <+> Plain . one <$>
          char '$' <+> esc <+> Plain . toText <$>
            some plainChar
   where
    plainChar =
      notFollowedBy (end <+> void (char '$') <+> escStart) *> anySingle

  escapeCode =
    msum
      [ c <$ char e | (c, e) <- escapeCodes ]
    <+> anySingle

-- | Gets all of the arguments for a function.
argExpr :: Parser (Params NExprLoc)
argExpr =
  msum
    [ atLeft
    , onlyname
    , atRight
    ]
  <* symbol ":"
 where
  -- An argument not in curly braces. There's some potential ambiguity
  -- in the case of, for example `x:y`. Is it a lambda function `x: y`, or
  -- a URI `x:y`? Nix syntax says it's the latter. So we need to fail if
  -- there's a valid URI parse here.
  onlyname =
    msum
      [ nixUri *> unexpected (Label ('v' :| "alid uri"))
      , Param <$> identifier
      ]

  -- Parameters named by an identifier on the left (`args @ {x, y}`)
  atLeft =
    try $
      do
        name               <- identifier <* symbol "@"
        (params, variadic) <- params
        pure $ ParamSet params variadic $ pure name

  -- Parameters named by an identifier on the right, or none (`{x, y} @ args`)
  atRight =
    do
      (params, variadic) <- params
      name               <- optional $ symbol "@" *> identifier
      pure $ ParamSet params variadic name

  -- Return the parameters set.
  params = braces getParams

  -- Collects the parameters within curly braces. Returns the parameters and
  -- a boolean indicating if the parameters are variadic.
  getParams :: Parser (ParamSet NExprLoc, Bool)
  getParams = go mempty
   where
    -- Attempt to parse `...`. If this succeeds, stop and return True.
    -- Otherwise, attempt to parse an argument, optionally with a
    -- default. If this fails, then return what has been accumulated
    -- so far.
    go acc = ((acc, True) <$ symbol "...") <+> getMore
     where
      getMore =
        -- Could be nothing, in which just return what we have so far.
        option (acc, False) $
          do
            -- Get an argument name and an optional default.
            pair <-
              liftA2 (,)
                identifier
                (optional $ question *> nixToplevelForm)

            let args = acc <> [pair]

            -- Either return this, or attempt to get a comma and restart.
            option (args, False) $ comma *> go args

nixBinders :: Parser [Binding NExprLoc]
nixBinders = (inherit <+> namedVar) `endBy` semi where
  inherit =
    do
      -- We can't use 'reserved' here because it would consume the whitespace
      -- after the keyword, which is not exactly the semantics of C++ Nix.
      try $ string "inherit" *> lookAhead (void (satisfy reservedEnd))
      p <- getSourcePos
      x <- whiteSpace *> optional scope
      liftA2 (Inherit x)
        (many keyName)
        (pure p)
        <?> "inherited binding"
  namedVar =
    do
      p <- getSourcePos
      liftA3 NamedVar
        (annotated <$> nixSelector)
        (equals *> nixToplevelForm)
        (pure p)
        <?> "variable binding"
  scope = nixParens <?> "inherit scope"

keyName :: Parser (NKeyName NExprLoc)
keyName = dynamicKey <+> staticKey
 where
  staticKey  = StaticKey <$> identifier
  dynamicKey = DynamicKey <$> nixAntiquoted nixString'

nixSet :: Parser NExprLoc
nixSet = annotateLocation1 ((isRec <*> braces nixBinders) <?> "set")
 where
  isRec = (reserved "rec" $> NSet Recursive <?> "recursive set") <+> pure (NSet NonRecursive)

parseNixFile :: MonadFile m => FilePath -> m (Result NExpr)
parseNixFile =
  parseFromFileEx $ stripAnnotation <$> (whiteSpace *> nixToplevelForm <* eof)

parseNixFileLoc :: MonadFile m => FilePath -> m (Result NExprLoc)
parseNixFileLoc = parseFromFileEx (whiteSpace *> nixToplevelForm <* eof)

parseNixText :: Text -> Result NExpr
parseNixText =
  parseFromText $ stripAnnotation <$> (whiteSpace *> nixToplevelForm <* eof)

parseNixTextLoc :: Text -> Result NExprLoc
parseNixTextLoc = parseFromText (whiteSpace *> nixToplevelForm <* eof)

{- Parser.Library -}

skipLineComment' :: Tokens Text -> Parser ()
skipLineComment' prefix =
  string prefix *> void (takeWhileP (pure "character") (\x -> x /= '\n' && x /= '\r'))

whiteSpace :: Parser ()
whiteSpace = do
  put =<< getSourcePos
  Lexer.space space1 lineCmnt blockCmnt
 where
  lineCmnt  = skipLineComment' "#"
  blockCmnt = Lexer.skipBlockComment "/*" "*/"

lexeme :: Parser a -> Parser a
lexeme p = p <* whiteSpace

symbol :: Text -> Parser Text
symbol = lexeme . string

reservedEnd :: Char -> Bool
reservedEnd x =
  isSpace x || (`elem` ("{([})];:.\"'," :: String)) x
{-# inline reservedEnd #-}

reserved :: Text -> Parser ()
reserved n =
  lexeme $ try $ string n *> lookAhead (void (satisfy reservedEnd) <|> eof)

identifier :: Parser VarName
identifier = lexeme $ try $ do
  (coerce -> ident) <-
    liftA2 cons
      (satisfy (\x -> isAlpha x || x == '_'))
      (takeWhileP mempty identLetter)
  guard $ not $ ident `HashSet.member` reservedNames
  pure ident
 where
  identLetter x = isAlphanumeric x || x == '_' || x == '\'' || x == '-'

-- We restrict the type of 'parens' and 'brackets' here because if they were to
-- take a @Parser NExprLoc@ argument they would parse additional text which
-- wouldn't be captured in the source location annotation.
--
-- Braces and angles in hnix don't enclose a single expression so this type
-- restriction would not be useful.
parens :: Parser (NExprF f) -> Parser (NExprF f)
parens   = between (symbol "(") (symbol ")")
braces :: ParsecT Void Text (State SourcePos) a -> ParsecT Void Text (State SourcePos) a
braces   = between (symbol "{") (symbol "}")
-- angles    = between (symbol "<") (symbol ">")
brackets :: Parser (NExprF f) -> Parser (NExprF f)
brackets = between (symbol "[") (symbol "]")
semi :: Parser Text
semi     = symbol ";"
comma :: Parser Text
comma    = symbol ","
-- colon     = symbol ":"
-- dot       = symbol "."
equals :: Parser Text
equals   = symbol "="
question :: Parser Text
question = symbol "?"

integer :: Parser Integer
integer = lexeme Lexer.decimal

float :: Parser Double
float = lexeme Lexer.float

reservedNames :: HashSet VarName
reservedNames =
  HashSet.fromList
    ["let", "in", "if", "then", "else", "assert", "with", "rec", "inherit"]

type Parser = ParsecT Void Text (State SourcePos)

type Result a = Either (Doc Void) a

parseFromFileEx :: MonadFile m => Parser a -> FilePath -> m (Result a)
parseFromFileEx parser file =
  do
    input <- decodeUtf8 <$> readFile file

    pure $
      either
        (Left . pretty . errorBundlePretty)
        pure
        $ (`evalState` initialPos file) $ runParserT parser file input

parseFromText :: Parser a -> Text -> Result a
parseFromText parser input =
  let stub = "<string>" in
  either
    (Left . pretty . errorBundlePretty)
    pure
    $ (`evalState` initialPos stub) $ (`runParserT` stub) parser input

{- Parser.Operators -}

data NSpecialOp = NHasAttrOp | NSelectOp
  deriving (Eq, Ord, Generic, Typeable, Data, Show, NFData)

data NAssoc = NAssocNone | NAssocLeft | NAssocRight
  deriving (Eq, Ord, Generic, Typeable, Data, Show, NFData)

data NOperatorDef
  = NUnaryDef   Text NUnaryOp
  | NBinaryDef  Text NBinaryOp  NAssoc
  | NSpecialDef Text NSpecialOp NAssoc
  deriving (Eq, Ord, Generic, Typeable, Data, Show, NFData)

annotateLocation :: Parser a -> Parser (Ann SrcSpan a)
annotateLocation p =
  do
    begin <- getSourcePos
    res <- p
    end   <- get -- The state set before the last whitespace

    pure $ Ann (SrcSpan begin end) res

annotateLocation1 :: Parser (NExprF NExprLoc) -> Parser NExprLoc
annotateLocation1 = fmap annToAnnF . annotateLocation

manyUnaryOp :: MonadPlus f => f (a -> a) -> f (a -> a)
manyUnaryOp f = foldr1 (.) <$> some f

operator :: Text -> Parser Text
operator op =
  case op of
    "-" -> tuneLexer "-" '>'
    "/" -> tuneLexer "/" '/'
    "<" -> tuneLexer "<" '='
    ">" -> tuneLexer ">" '='
    n   -> symbol n
 where
  tuneLexer opchar nonextchar =
    lexeme . try $ string opchar <* notFollowedBy (char nonextchar)

opWithLoc :: Text -> o -> (Ann SrcSpan o -> a) -> Parser a
opWithLoc name op f =
  do
    Ann ann _ <-
      annotateLocation $
        {- dbg (toString name) $ -}
        operator name

    pure $ f $ Ann ann op

binaryN :: Text -> NBinaryOp -> (NOperatorDef, Operator (ParsecT Void Text (State SourcePos)) NExprLoc)
binaryN name op =
  (NBinaryDef name op NAssocNone, InfixN $ opWithLoc name op nBinary)
binaryL :: Text -> NBinaryOp -> (NOperatorDef, Operator (ParsecT Void Text (State SourcePos)) NExprLoc)
binaryL name op =
  (NBinaryDef name op NAssocLeft, InfixL $ opWithLoc name op nBinary)
binaryR :: Text -> NBinaryOp -> (NOperatorDef, Operator (ParsecT Void Text (State SourcePos)) NExprLoc)
binaryR name op =
  (NBinaryDef name op NAssocRight, InfixR $ opWithLoc name op nBinary)
prefix :: Text -> NUnaryOp -> (NOperatorDef, Operator (ParsecT Void Text (State SourcePos)) NExprLoc)
prefix name op =
  (NUnaryDef name op, Prefix $ manyUnaryOp $ opWithLoc name op nUnary)
-- postfix name op = (NUnaryDef name op,
--                    Postfix (opWithLoc name op nUnary))

nixOperators
  :: Parser (Ann SrcSpan (NAttrPath NExprLoc))
  -> [[(NOperatorDef, Operator Parser NExprLoc)]]
nixOperators selector =
  [ -- This is not parsed here, even though technically it's part of the
    -- expression table. The problem is that in some cases, such as list
    -- membership, it's also a term. And since terms are effectively the
    -- highest precedence entities parsed by the expression parser, it ends up
    -- working out that we parse them as a kind of "meta-term".

    -- {-  1 -} [ (NSpecialDef "." NSelectOp NAssocLeft,
    --             Postfix $ do
    --                    sel <- seldot *> selector
    --                    mor <- optional (reserved "or" *> term)
    --                    pure $ \x -> nSelectLoc x sel mor) ]

    {-  2 -}
    [ ( NBinaryDef " " NApp NAssocLeft
      ,
        -- Thanks to Brent Yorgey for showing me this trick!
        InfixL $ nApp <$ symbol ""
      )
    ]
  , {-  3 -}
    [ prefix  "-"  NNeg ]
  , {-  4 -}
    [ ( NSpecialDef "?" NHasAttrOp NAssocLeft
      , Postfix $ symbol "?" *> (flip nHasAttr <$> selector)
      )
    ]
  , {-  5 -}
    [ binaryR "++" NConcat ]
  , {-  6 -}
    [ binaryL "*"  NMult
    , binaryL "/"  NDiv
    ]
  , {-  7 -}
    [ binaryL "+"  NPlus
    , binaryL "-"  NMinus
    ]
  , {-  8 -}
    [ prefix  "!"  NNot ]
  , {-  9 -}
    [ binaryR "//" NUpdate ]
  , {- 10 -}
    [ binaryL "<"  NLt
    , binaryL ">"  NGt
    , binaryL "<=" NLte
    , binaryL ">=" NGte
    ]
  , {- 11 -}
    [ binaryN "==" NEq
    , binaryN "!=" NNEq
    ]
  , {- 12 -}
    [ binaryL "&&" NAnd ]
  , {- 13 -}
    [ binaryL "||" NOr ]
  , {- 14 -}
    [ binaryR "->" NImpl ]
  ]

data OperatorInfo = OperatorInfo
  { precedence    :: Int
  , associativity :: NAssoc
  , operatorName  :: Text
  } deriving (Eq, Ord, Generic, Typeable, Data, Show)

getUnaryOperator :: NUnaryOp -> OperatorInfo
getUnaryOperator = (m Map.!)
 where
  m =
    Map.fromList $
      concat $
        zipWith
          buildEntry
          [1 ..]
          (nixOperators $ fail "unused")

  buildEntry i =
    concatMap $
      \case
        (NUnaryDef name op, _) -> [(op, OperatorInfo i NAssocNone name)]
        _                      -> mempty

getBinaryOperator :: NBinaryOp -> OperatorInfo
getBinaryOperator = (m Map.!)
 where
  m =
    Map.fromList $
      concat $
        zipWith
          buildEntry
          [1 ..]
          (nixOperators $ fail "unused")

  buildEntry i =
    concatMap $
      \case
        (NBinaryDef name op assoc, _) -> [(op, OperatorInfo i assoc name)]
        _                             -> mempty

getSpecialOperator :: NSpecialOp -> OperatorInfo
getSpecialOperator NSelectOp = OperatorInfo 1 NAssocLeft "."
getSpecialOperator o         = m Map.! o
 where
  m =
    Map.fromList $
      concat $
        zipWith
          buildEntry
          [1 ..]
          (nixOperators $ fail "unused")

  buildEntry i =
    concatMap $
      \case
        (NSpecialDef name op assoc, _) -> [(op, OperatorInfo i assoc name)]
        _                              -> mempty
