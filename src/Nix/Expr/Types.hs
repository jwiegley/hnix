{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveDataTypeable #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

-- | The Nix expression type and supporting types.
--
-- For a brief introduction of the Nix expression language, see
-- <https://nixos.org/nix/manual/#ch-expression-language>.
module Nix.Expr.Types where

#ifdef MIN_VERSION_serialise
import qualified Codec.Serialise                ( Serialise(decode, encode) )  -- For instance implementation function disamburgation
import           Codec.Serialise                ( Serialise )
#endif
import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad
import           Data.Aeson
import           Data.Aeson.TH
import           Data.Binary                    ( Binary )
import qualified Data.Binary                   as Bin
import           Data.Data
import           Data.Eq.Deriving
import           Data.Fix
import           Data.Functor.Classes
import           Data.Hashable
import           Data.Hashable.Lifted
import           Data.Interned.Text
import           Data.Interned
import           Data.List                      ( inits
                                                , tails
                                                )
import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty            as NE
import           Data.Maybe                     ( fromMaybe )
import           Data.Ord.Deriving
import           Data.Text                      ( Text
                                                , pack
                                                , unpack
                                                )
import           Data.Traversable
import           GHC.Exts
import           GHC.Generics                 hiding ( Prefix )
import           Language.Haskell.TH.Syntax
import           Lens.Family2
import           Lens.Family2.TH
import           Nix.Atoms
import           Nix.Utils
import           Text.Megaparsec.Pos
import           Text.Read.Deriving
import           Text.Show.Deriving
import           Type.Reflection                ( eqTypeRep )
import qualified Type.Reflection               as Reflection



hashAt :: VarName -> Lens' (AttrSet v) (Maybe v)
hashAt = flip alterF

-- unfortunate orphans
instance Hashable1 NonEmpty

-- | The main Nix expression type. As it is polimophic, has a functor,
-- which allows to traverse expressions and map functions over them.
-- The actual 'NExpr' type is a fixed point of this functor, defined
-- below.
data NExprF r
  = NConstant !NAtom
  -- ^ Constants: ints, floats, bools, URIs, and null.
  | NStr !(NString r)
  -- ^ A string, with interpolated expressions.
  | NSym !VarName
  -- ^ A variable. For example, in the expression @f a@, @f@ is represented
  -- as @NSym "f"@ and @a@ as @NSym "a"@.
  --
  -- > NSym "x"                                    ~  x
  | NList ![r]
  -- ^ A list literal.
  --
  -- > NList [x,y]                                 ~  [ x y ]
  | NSet !NRecordType ![Binding r]
  -- ^ An attribute set literal
  --
  -- > NSet NRecursive    [NamedVar x y _]         ~  rec { x = y; }
  -- > NSet NNonRecursive [Inherit Nothing [x] _]  ~  { inherit x; }
  | NLiteralPath !FilePath
  -- ^ A path expression, which is evaluated to a store path. The path here
  -- can be relative, in which case it's evaluated relative to the file in
  -- which it appears.
  --
  -- > NLiteralPath "/x"                           ~  /x
  -- > NLiteralPath "x/y"                          ~  x/y
  | NEnvPath !FilePath
  -- ^ A path which refers to something in the Nix search path (the NIX_PATH
  -- environment variable. For example, @<nixpkgs/pkgs>@.
  --
  -- > NEnvPath "x"                                ~  <x>
  | NUnary !NUnaryOp !r
  -- ^ Application of a unary operator to an expression.
  --
  -- > NUnary NNeg x                               ~  - x
  -- > NUnary NNot x                               ~  ! x
  | NBinary !NBinaryOp !r !r
  -- ^ Application of a binary operator to two expressions.
  --
  -- > NBinary NPlus x y                           ~  x + y
  -- > NBinary NApp  f x                           ~  f x
  | NSelect !r !(NAttrPath r) !(Maybe r)
  -- ^ Dot-reference into an attribute set, optionally providing an
  -- alternative if the key doesn't exist.
  --
  -- > NSelect s (x :| []) Nothing                 ~  s.x
  -- > NSelect s (x :| []) (Just y)                ~  s.x or y
  | NHasAttr !r !(NAttrPath r)
  -- ^ Ask if a set contains a given attribute path.
  --
  -- > NHasAttr s (x :| [])                        ~  s ? x
  | NAbs !(Params r) !r
  -- ^ A function literal (lambda abstraction).
  --
  -- > NAbs (Param "x") y                          ~  x: y
  | NLet ![Binding r] !r
  -- ^ Evaluate the second argument after introducing the bindings.
  --
  -- > NLet []                    x                ~  let in x
  -- > NLet [NamedVar x y _]      z                ~  let x = y; in z
  -- > NLet [Inherit Nothing x _] y                ~  let inherit x; in y
  | NIf !r !r !r
  -- ^ If-then-else statement.
  --
  -- > NIf x y z                                   ~  if x then y else z
  | NWith !r !r
  -- ^ Evaluate an attribute set, bring its bindings into scope, and
  -- evaluate the second argument.
  --
  -- > NWith x y                                   ~  with x; y
  | NAssert !r !r
  -- ^ Assert that the first returns @true@ before evaluating the second.
  --
  -- > NAssert x y                                 ~  assert x; y
  | NSynHole !VarName
  -- ^ Syntactic hole.
  --
  -- See <https://github.com/haskell-nix/hnix/issues/197> for context.
  --
  -- > NSynHole "x"                                ~  ^x
  deriving (Ord, Eq, Generic, Generic1, Typeable, Data, Functor,
            Foldable, Traversable, Show, NFData, Hashable)

instance Hashable1 NExprF

instance NFData1 NExprF

#ifdef MIN_VERSION_serialise
instance Serialise r => Serialise (NExprF r)
#endif

-- | We make an `IsString` for expressions, where the string is interpreted
-- as an identifier. This is the most common use-case...
instance IsString NExpr where
  fromString = Fix . NSym . fromString

--instance Lift VarName where
--  lift 

instance Lift (Fix NExprF) where
  lift = dataToExpQ $ \b ->
    case Reflection.typeOf b `eqTypeRep` Reflection.typeRep @Text of
      Just HRefl -> Just [| pack $(liftString $ unpack b) |]
      Nothing    -> 
        case Reflection.typeOf b `eqTypeRep` Reflection.typeRep @VarName of
          Just HRefl -> Just [| intern $ pack $ $(liftString $ unpack $ unintern b) |]
          Nothing    -> Nothing

#if MIN_VERSION_template_haskell(2,17,0)
  liftTyped = unsafeCodeCoerce . lift
#elif MIN_VERSION_template_haskell(2,16,0)
  liftTyped = unsafeTExpCoerce . lift
#endif

-- | The monomorphic expression type is a fixed point of the polymorphic one.
type NExpr = Fix NExprF

#ifdef MIN_VERSION_serialise
instance Serialise NExpr
#endif

-- | A single line of the bindings section of a let expression or of a set.
data Binding r
  = NamedVar !(NAttrPath r) !r !SourcePos
  -- ^ An explicit naming.
  --
  -- > NamedVar (StaticKey "x" :| [StaticKey "y"]) z SourcePos{}  ~  x.y = z;
  | Inherit !(Maybe r) ![NKeyName r] !SourcePos
  -- ^ Using a name already in scope, such as @inherit x;@ which is shorthand
  --   for @x = x;@ or @inherit (x) y;@ which means @y = x.y;@. The
  --   @unsafeGetAttrPos@ for every name so inherited is the position of the
  --   first name, whether that be the first argument to this constructor, or
  --   the first member of the list in the second argument.
  --
  -- > Inherit Nothing  [StaticKey "x"] SourcePos{}               ~  inherit x;
  -- > Inherit (Just x) []              SourcePos{}               ~  inherit (x);
  deriving (Generic, Generic1, Typeable, Data, Ord, Eq, Functor,
            Foldable, Traversable, Show, NFData, Hashable)

instance Hashable1 Binding

instance NFData1 Binding

#ifdef MIN_VERSION_serialise
instance Serialise r => Serialise (Binding r)
#endif

-- | @Params@ represents all the ways the formal parameters to a
-- function can be represented.
data Params r
  = Param !VarName
  -- ^ For functions with a single named argument, such as @x: x + 1@.
  --
  -- > Param "x"                                  ~  x
  | ParamSet !(ParamSet r) !Bool !(Maybe VarName)
  -- ^ Explicit parameters (argument must be a set). Might specify a name to
  -- bind to the set in the function body. The bool indicates whether it is
  -- variadic or not.
  --
  -- > ParamSet [("x",Nothing)] False Nothing     ~  { x }
  -- > ParamSet [("x",Just y)]  True  (Just "s")  ~  s@{ x ? y, ... }
  deriving (Ord, Eq, Generic, Generic1, Typeable, Data, Functor, Show,
            Foldable, Traversable, NFData, Hashable)

instance Hashable1 Params

instance NFData1 Params

#ifdef MIN_VERSION_serialise
instance Serialise r => Serialise (Params r)
#endif

-- This uses an association list because nix XML serialization preserves the
-- order of the param set.
type ParamSet r = [(VarName, Maybe r)]

instance IsString (Params r) where
  fromString = Param . fromString

-- | 'Antiquoted' represents an expression that is either
-- antiquoted (surrounded by ${...}) or plain (not antiquoted).
data Antiquoted (v :: *) (r :: *)
  = Plain !v
  | EscapedNewline
  -- ^ 'EscapedNewline' corresponds to the special newline form
  --
  -- > ''\n
  --
  -- in an indented string. It is equivalent to a single newline character:
  --
  -- > ''''\n''  ≡  "\n"
  | Antiquoted !r
  deriving (Ord, Eq, Generic, Generic1, Typeable, Data, Functor, Foldable,
            Traversable, Show, Read, NFData, Hashable)

instance Hashable v => Hashable1 (Antiquoted v)

instance Hashable2 Antiquoted where
  liftHashWithSalt2 ha _ salt (Plain a) = ha (salt `hashWithSalt` (0 :: Int)) a
  liftHashWithSalt2 _ _ salt EscapedNewline = salt `hashWithSalt` (1 :: Int)
  liftHashWithSalt2 _ hb salt (Antiquoted b) =
    hb (salt `hashWithSalt` (2 :: Int)) b

instance NFData v => NFData1 (Antiquoted v)

#ifdef MIN_VERSION_serialise
instance (Serialise v, Serialise r) => Serialise (Antiquoted v r)
#endif

-- | An 'NString' is a list of things that are either a plain string
-- or an antiquoted expression. After the antiquotes have been evaluated,
-- the final string is constructed by concatenating all the parts.
data NString r
  = DoubleQuoted ![Antiquoted Text r]
  -- ^ Strings wrapped with double-quotes (") can contain literal newline
  -- characters, but the newlines are preserved and no indentation is stripped.
  --
  -- > DoubleQuoted [Plain "x",Antiquoted y]   ~  "x${y}"
  | Indented !Int ![Antiquoted Text r]
  -- ^ Strings wrapped with two single quotes ('') can contain newlines, and
  --   their indentation will be stripped, but the amount stripped is
  --   remembered.
  --
  -- > Indented 1 [Plain "x"]                  ~  '' x''
  -- >
  -- > Indented 0 [EscapedNewline]             ~  ''''\n''
  -- >
  -- > Indented 0 [Plain "x\n ",Antiquoted y]  ~  ''
  -- >                                            x
  -- >                                             ${y}''
  deriving (Eq, Ord, Generic, Generic1, Typeable, Data, Functor, Foldable,
            Traversable, Show, Read, NFData, Hashable)

instance Hashable1 NString

instance NFData1 NString

#ifdef MIN_VERSION_serialise
instance Serialise r => Serialise (NString r)
#endif

-- | For the the 'IsString' instance, we use a plain doublequoted string.
instance IsString (NString r) where
  fromString ""     = DoubleQuoted []
  fromString string = DoubleQuoted [Plain $ pack string]

-- | A 'KeyName' is something that can appear on the left side of an
-- equals sign. For example, @a@ is a 'KeyName' in @{ a = 3; }@, @let a = 3;
-- in ...@, @{}.a@ or @{} ? a@.
--
-- Nix supports both static keynames (just an identifier) and dynamic
-- identifiers. Dynamic identifiers can be either a string (e.g.:
-- @{ "a" = 3; }@) or an antiquotation (e.g.: @let a = "example";
-- in { ${a} = 3; }.example@).
--
-- Note: There are some places where a dynamic keyname is not allowed.
-- In particular, those include:
--
--   * The RHS of a @binding@ inside @let@: @let ${"a"} = 3; in ...@
--     produces a syntax error.
--   * The attribute names of an 'inherit': @inherit ${"a"};@ is forbidden.
--
-- Note: In Nix, a simple string without antiquotes such as @"foo"@ is
-- allowed even if the context requires a static keyname, but the
-- parser still considers it a 'DynamicKey' for simplicity.
data NKeyName r
  = DynamicKey !(Antiquoted (NString r) r)
  -- ^
  -- > DynamicKey (Plain (DoubleQuoted [Plain "x"]))     ~  "x"
  -- > DynamicKey (Antiquoted x)                         ~  ${x}
  -- > DynamicKey (Plain (DoubleQuoted [Antiquoted x]))  ~  "${x}"
  | StaticKey !VarName
  -- ^
  -- > StaticKey "x"                                     ~  x
  deriving (Eq, Ord, Generic, Typeable, Data, Show, Read, NFData, Hashable)

#ifdef MIN_VERSION_serialise
instance Serialise r => Serialise (NKeyName r)

instance Serialise Pos where
  encode x = Codec.Serialise.encode (unPos x)
  decode = mkPos <$> Codec.Serialise.decode

instance Serialise SourcePos where
  encode (SourcePos f l c) = Codec.Serialise.encode f <> Codec.Serialise.encode l <> Codec.Serialise.encode c
  decode = SourcePos <$> Codec.Serialise.decode <*> Codec.Serialise.decode <*> Codec.Serialise.decode
#endif

instance Hashable Pos where
  hashWithSalt salt x = hashWithSalt salt (unPos x)

instance Hashable SourcePos where
  hashWithSalt salt (SourcePos f l c) =
    salt `hashWithSalt` f `hashWithSalt` l `hashWithSalt` c

instance NFData1 NKeyName where
  liftRnf _ (StaticKey  !_            ) = ()
  liftRnf _ (DynamicKey (Plain !_)    ) = ()
  liftRnf _ (DynamicKey EscapedNewline) = ()
  liftRnf k (DynamicKey (Antiquoted r)) = k r

-- | Most key names are just static text, so this instance is convenient.
instance IsString (NKeyName r) where
  fromString = StaticKey . fromString

instance Eq1 NKeyName where
  liftEq eq (DynamicKey a) (DynamicKey b) = liftEq2 (liftEq eq) eq a b
  liftEq _  (StaticKey  a) (StaticKey  b) = a == b
  liftEq _  _              _              = False

-- | @since 0.10.1
instance Ord1 NKeyName where
  liftCompare cmp (DynamicKey a) (DynamicKey b) = liftCompare2 (liftCompare cmp) cmp a b
  liftCompare _   (DynamicKey _) (StaticKey _)  = LT
  liftCompare _   (StaticKey _)  (DynamicKey _) = GT
  liftCompare _   (StaticKey a)  (StaticKey b)  = compare a b

instance Hashable1 NKeyName where
  liftHashWithSalt h salt (DynamicKey a) =
    liftHashWithSalt2 (liftHashWithSalt h) h (salt `hashWithSalt` (0 :: Int)) a
  liftHashWithSalt _ salt (StaticKey n) =
    salt `hashWithSalt` (1 :: Int) `hashWithSalt` n

-- Deriving this instance automatically is not possible because @r@
-- occurs not only as last argument in @Antiquoted (NString r) r@
instance Show1 NKeyName where
  liftShowsPrec sp sl p = \case
    DynamicKey a -> showsUnaryWith
      (liftShowsPrec2 (liftShowsPrec sp sl) (liftShowList sp sl) sp sl)
      "DynamicKey"
      p
      a
    StaticKey t -> showsUnaryWith showsPrec "StaticKey" p t

-- Deriving this instance automatically is not possible because @r@
-- occurs not only as last argument in @Antiquoted (NString r) r@
instance Functor NKeyName where
  fmap = fmapDefault

-- Deriving this instance automatically is not possible because @r@
-- occurs not only as last argument in @Antiquoted (NString r) r@
instance Foldable NKeyName where
  foldMap = foldMapDefault

-- Deriving this instance automatically is not possible because @r@
-- occurs not only as last argument in @Antiquoted (NString r) r@
instance Traversable NKeyName where
  traverse f = \case
    DynamicKey (Plain      str) -> DynamicKey . Plain <$> traverse f str
    DynamicKey (Antiquoted e  ) -> DynamicKey . Antiquoted <$> f e
    DynamicKey EscapedNewline   -> pure $ DynamicKey EscapedNewline
    StaticKey  key              -> pure (StaticKey key)

-- | A selector (for example in a @let@ or an attribute set) is made up
-- of strung-together key names.
--
-- > StaticKey "x" :| [DynamicKey (Antiquoted y)]  ~  x.${y}
type NAttrPath r = NonEmpty (NKeyName r)

-- | There are two unary operations: logical not and integer negation.
data NUnaryOp
  = NNeg  -- ^ @-@
  | NNot  -- ^ @!@
  deriving (Eq, Ord, Enum, Bounded, Generic, Typeable, Data, Show, Read,
            NFData, Hashable)

#ifdef MIN_VERSION_serialise
instance Serialise NUnaryOp
#endif

-- | Binary operators expressible in the nix language.
data NBinaryOp
  = NEq      -- ^ Equality (@==@)
  | NNEq     -- ^ Inequality (@!=@)
  | NLt      -- ^ Less than (@<@)
  | NLte     -- ^ Less than or equal (@<=@)
  | NGt      -- ^ Greater than (@>@)
  | NGte     -- ^ Greater than or equal (@>=@)
  | NAnd     -- ^ Logical and (@&&@)
  | NOr      -- ^ Logical or (@||@)
  | NImpl    -- ^ Logical implication (@->@)
  | NUpdate  -- ^ Joining two attribute sets (@//@)
  | NPlus    -- ^ Addition (@+@)
  | NMinus   -- ^ Subtraction (@-@)
  | NMult    -- ^ Multiplication (@*@)
  | NDiv     -- ^ Division (@/@)
  | NConcat  -- ^ List concatenation (@++@)
  | NApp     -- ^ Apply a function to an argument.
             --
             -- > NBinary NApp f x  ~  f x
  deriving (Eq, Ord, Enum, Bounded, Generic, Typeable, Data, Show, Read,
            NFData, Hashable)

#ifdef MIN_VERSION_serialise
instance Serialise NBinaryOp
#endif

-- | 'NRecordType' distinguishes between recursive and non-recursive attribute
-- sets.
data NRecordType
  = NNonRecursive  -- ^ >     { ... }
  | NRecursive     -- ^ > rec { ... }
  deriving (Eq, Ord, Enum, Bounded, Generic, Typeable, Data, Show, Read,
            NFData, Hashable)

#ifdef MIN_VERSION_serialise
instance Serialise NRecordType
#endif

-- | Get the name out of the parameter (there might be none).
paramName :: Params r -> Maybe VarName
paramName (Param n       ) = Just n
paramName (ParamSet _ _ n) = n

$(deriveEq1 ''NExprF)
$(deriveEq1 ''NString)
$(deriveEq1 ''Binding)
$(deriveEq1 ''Params)
$(deriveEq1 ''Antiquoted)
$(deriveEq2 ''Antiquoted)

$(deriveOrd1 ''NExprF)
$(deriveOrd1 ''NString)
$(deriveOrd1 ''Binding)
$(deriveOrd1 ''Params)
$(deriveOrd1 ''Antiquoted)
$(deriveOrd2 ''Antiquoted)

$(deriveRead1 ''NString)
$(deriveRead1 ''Params)
$(deriveRead1 ''Antiquoted)
$(deriveRead2 ''Antiquoted)

$(deriveShow1 ''NExprF)
$(deriveShow1 ''NString)
$(deriveShow1 ''Params)
$(deriveShow1 ''Binding)
$(deriveShow1 ''Antiquoted)
$(deriveShow2 ''Antiquoted)

--x $(deriveJSON1 defaultOptions ''NExprF)
$(deriveJSON1 defaultOptions ''NString)
$(deriveJSON1 defaultOptions ''Params)
--x $(deriveJSON1 defaultOptions ''Binding)
$(deriveJSON1 defaultOptions ''Antiquoted)
$(deriveJSON2 defaultOptions ''Antiquoted)

instance (Binary v, Binary a) => Binary (Antiquoted v a)
instance Binary a => Binary (NString a)
instance Binary a => Binary (Binding a)
instance Binary Pos where
  put x = Bin.put (unPos x)
  get = mkPos <$> Bin.get
instance Binary SourcePos
instance Binary a => Binary (NKeyName a)
instance Binary a => Binary (Params a)
instance Binary NAtom
instance Binary NUnaryOp
instance Binary NBinaryOp
instance Binary NRecordType
instance Binary a => Binary (NExprF a)

instance ToJSON VarName where
  toJSON = toJSON . unintern
instance (ToJSON v, ToJSON a) => ToJSON (Antiquoted v a)
instance ToJSON a => ToJSON (NString a)
instance ToJSON a => ToJSON (Binding a)
instance ToJSON Pos where
  toJSON x = toJSON (unPos x)
instance ToJSON SourcePos
instance ToJSON a => ToJSON (NKeyName a)
instance ToJSON a => ToJSON (Params a)
instance ToJSON NAtom
instance ToJSON NUnaryOp
instance ToJSON NBinaryOp
instance ToJSON NRecordType
instance ToJSON a => ToJSON (NExprF a)

instance FromJSON VarName where parseJSON = fmap (fmap intern) $ parseJSON @Text
instance (FromJSON v, FromJSON a) => FromJSON (Antiquoted v a)
instance FromJSON a => FromJSON (NString a)
instance FromJSON a => FromJSON (Binding a)
instance FromJSON Pos where
  parseJSON = fmap mkPos . parseJSON
instance FromJSON SourcePos
instance FromJSON a => FromJSON (NKeyName a)
instance FromJSON a => FromJSON (Params a)
instance FromJSON NAtom
instance FromJSON NUnaryOp
instance FromJSON NBinaryOp
instance FromJSON NRecordType
instance FromJSON a => FromJSON (NExprF a)

$(makeTraversals ''NExprF)
$(makeTraversals ''Binding)
$(makeTraversals ''Params)
$(makeTraversals ''Antiquoted)
$(makeTraversals ''NString)
$(makeTraversals ''NKeyName)
$(makeTraversals ''NUnaryOp)
$(makeTraversals ''NBinaryOp)

--x $(makeLenses ''Fix)

class NExprAnn ann g | g -> ann where
    fromNExpr :: g r -> (NExprF r, ann)
    toNExpr :: (NExprF r, ann) -> g r

ekey
  :: NExprAnn ann g
  => NonEmpty VarName
  -> SourcePos
  -> Lens' (Fix g) (Maybe (Fix g))
ekey keys pos f e@(Fix x) | (NSet NNonRecursive xs, ann) <- fromNExpr x = case go xs of
  ((v, []      ) : _) -> fromMaybe e <$> f (Just v)
  ((v, r : rest) : _) -> ekey (r :| rest) pos f v

  _                   -> f Nothing <&> \case
    Nothing -> e
    Just v ->
      let entry = NamedVar (NE.map StaticKey keys) v pos
      in  Fix (toNExpr (NSet NNonRecursive (entry : xs), ann))
 where
  go xs = do
    let keys' = NE.toList keys
    (ks, rest) <- zip (inits keys') (tails keys')
    case ks of
      []     -> empty
      j : js -> do
        NamedVar ns v _p <- xs
        guard $ (j : js) == (NE.toList ns ^.. traverse . _StaticKey)
        pure (v, rest)

ekey _ _ f e = fromMaybe e <$> f Nothing

stripPositionInfo :: NExpr -> NExpr
stripPositionInfo = transport phi
 where
  phi (NSet recur binds) = NSet recur (map go binds)
  phi (NLet binds body) = NLet (map go binds) body
  phi x                 = x

  go (NamedVar path r     _pos) = NamedVar path r nullPos
  go (Inherit  ms   names _pos) = Inherit ms names nullPos

nullPos :: SourcePos
nullPos = SourcePos "<string>" (mkPos 1) (mkPos 1)
