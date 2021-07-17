{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

-- | The Nix expression type and supporting types.
--
-- For a brief introduction of the Nix expression language, see
-- <https://nixos.org/nix/manual/#ch-expression-language>.
--
-- This module is a beginning of a deep embedding (term) of a Nix language into Haskell.
-- Shallow/deep embedding brief:
-- <https://web.archive.org/web/20201112031804/https://alessandrovermeulen.me/2013/07/13/the-difference-between-shallow-and-deep-embedding/>
--
-- (additiona info for dev): Big use of TemplateHaskell in the module requires proper (top-down) organization of declarations
module Nix.Expr.Types where

import qualified Codec.Serialise                as Serialise
import           Codec.Serialise                ( Serialise )
import           Control.DeepSeq
import           Data.Aeson
import           Data.Aeson.TH
import qualified Data.Binary                   as Binary
import           Data.Binary                    ( Binary )
import           Data.Data
import           Data.Fix
import           Data.Functor.Classes
import           Data.Hashable.Lifted
import qualified Data.HashMap.Lazy             as MapL
import qualified Data.List.NonEmpty            as NE
import qualified Text.Show
import           Data.Traversable
import           GHC.Generics
import qualified Language.Haskell.TH.Syntax    as TH
import           Lens.Family2
import           Lens.Family2.TH
import           Text.Megaparsec.Pos            ( SourcePos(SourcePos)
                                                , Pos
                                                , mkPos
                                                , unPos
                                                )
import           Text.Show.Deriving
import           Text.Read.Deriving
import           Data.Eq.Deriving
import           Data.Ord.Deriving
import qualified Type.Reflection               as Reflection
import           Type.Reflection                ( eqTypeRep )
import           Nix.Atoms
import           Nix.Utils
#if !MIN_VERSION_text(1,2,4)
-- NOTE: Remove package @th-lift-instances@ removing this
import           Instances.TH.Lift              ()  -- importing Lift Text fo GHC 8.6
#endif


-- * Utilitary: orphan instances

-- Placed here because TH inference depends on declaration sequence.

-- Upstreaming so far was not pursued.

instance Serialise Pos where
  encode = Serialise.encode . unPos
  decode = mkPos <$> Serialise.decode

instance Serialise SourcePos where
  encode (SourcePos f l c) =
    Serialise.encode f <>
    Serialise.encode l <>
    Serialise.encode c
  decode =
    liftA3 SourcePos
      Serialise.decode
      Serialise.decode
      Serialise.decode

instance Hashable Pos where
  hashWithSalt salt = hashWithSalt salt . unPos

instance Hashable SourcePos where
  hashWithSalt salt (SourcePos f l c) =
    salt
      `hashWithSalt` f
      `hashWithSalt` l
      `hashWithSalt` c

instance Binary Pos where
  put = Binary.put . unPos
  get = mkPos <$> Binary.get
instance Binary SourcePos

instance ToJSON Pos where
  toJSON = toJSON . unPos
instance ToJSON SourcePos

instance FromJSON Pos where
  parseJSON = fmap mkPos . parseJSON
instance FromJSON SourcePos

-- | Holds file positionng information for abstrations.
-- A type synonym for @HashMap VarName SourcePos@.
type PositionSet = HashMap VarName SourcePos


-- * Components of Nix expressions

-- NExpr is a composition of
--   * direct reuse of the Haskell types (list, FilePath, Text)
--   * NAtom
--   * Types in this section
--   * Fixpoint nature

newtype VarName = VarName Text
  deriving
    ( Eq, Ord, Generic
    , Typeable, Data, NFData, Serialise, Binary, ToJSON, FromJSON
    , Show, Read, Hashable
    )

instance IsString VarName where
  fromString = coerce . fromString @Text

instance ToString VarName where
  toString = toString @Text . coerce

-- ** @Params@

--  2021-07-16: NOTE: Should replace @ParamSet@ List
-- | > Hashmap VarName -- type synonym
type AttrSet = HashMap VarName

-- This uses an association list because nix XML serialization preserves the
-- order of the param set.
type ParamSet r = [(VarName, Maybe r)]

-- | @Params@ represents all the ways the formal parameters to a
-- function can be represented.
data Params r
  = Param !VarName
  -- ^ For functions with a single named argument, such as @x: x + 1@.
  --
  -- > Param "x"                                  ~  x
  | ParamSet !(ParamSet r) !Bool !(Maybe VarName)
  --  2021-05-15: NOTE: Seems like we should flip the ParamSet, so partial application kicks in for Bool?
  --  2021-05-15: NOTE: '...' variadic property probably needs a Bool synonym.
  -- ^ Explicit parameters (argument must be a set). Might specify a name to
  -- bind to the set in the function body. The bool indicates whether it is
  -- variadic or not.
  --
  -- > ParamSet [("x",Nothing)] False Nothing     ~  { x }
  -- > ParamSet [("x",pure y)]  True  (pure "s")  ~  s@{ x ? y, ... }
  deriving
    ( Eq, Ord, Generic, Generic1
    , Typeable, Data, NFData, NFData1, Serialise, Binary, ToJSON, ToJSON1, FromJSON, FromJSON1
    , Functor, Foldable, Traversable
    , Show, Hashable, Hashable1
    )

instance IsString (Params r) where
  fromString = Param . fromString

$(deriveShow1 ''Params)
$(deriveRead1 ''Params)
$(deriveEq1   ''Params)
$(deriveOrd1  ''Params)

-- *** Lens traversals

$(makeTraversals ''Params)


-- ** @Antiquoted@

-- | 'Antiquoted' represents an expression that is either
-- antiquoted (surrounded by ${...}) or plain (not antiquoted).
data Antiquoted (v :: Type) (r :: Type)
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
  deriving
    ( Eq, Ord, Generic, Generic1
    , Typeable, Data, NFData, NFData1, Serialise, Binary
    , ToJSON, ToJSON1, FromJSON, FromJSON1
    , Functor, Foldable, Traversable
    , Show, Read, Hashable, Hashable1
    )

instance Hashable2 Antiquoted where
  liftHashWithSalt2 ha _  salt (Plain a)      = ha (salt `hashWithSalt` (0 :: Int)) a
  liftHashWithSalt2 _  _  salt EscapedNewline =     salt `hashWithSalt` (1 :: Int)
  liftHashWithSalt2 _  hb salt (Antiquoted b) = hb (salt `hashWithSalt` (2 :: Int)) b

$(deriveShow1 ''Antiquoted)
$(deriveShow2 ''Antiquoted)
$(deriveRead1 ''Antiquoted)
$(deriveRead2 ''Antiquoted)
$(deriveEq1   ''Antiquoted)
$(deriveEq2   ''Antiquoted)
$(deriveOrd1  ''Antiquoted)
$(deriveOrd2  ''Antiquoted)
$(deriveJSON2 defaultOptions ''Antiquoted)


-- *** Lens traversals

$(makeTraversals ''Antiquoted)


-- ** @NString@

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
  deriving
    ( Eq, Ord, Generic, Generic1
    , Typeable, Data, NFData, NFData1, Serialise, Binary, ToJSON, ToJSON1, FromJSON, FromJSON1
    , Functor, Foldable, Traversable
    , Show, Read, Hashable, Hashable1
    )

-- | For the the 'IsString' instance, we use a plain doublequoted string.
instance IsString (NString r) where
  fromString ""     = DoubleQuoted mempty
  fromString string = DoubleQuoted [Plain $ toText string]

$(deriveShow1 ''NString)
$(deriveRead1 ''NString)
$(deriveEq1   ''NString)
$(deriveOrd1  ''NString)

-- *** Lens traversals

$(makeTraversals ''NString)


-- ** @NKeyName@

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
--     produces a syntax fail.
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
  deriving
    ( Eq, Ord, Generic
    , Typeable, Data, NFData, Serialise, Binary, ToJSON, FromJSON
    , Show, Read, Hashable
    )

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
  liftCompare _   (DynamicKey _) (StaticKey  _) = LT
  liftCompare _   (StaticKey  _) (DynamicKey _) = GT
  liftCompare _   (StaticKey  a) (StaticKey  b) = compare a b

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
    StaticKey t -> showsUnaryWith Text.Show.showsPrec "StaticKey" p t

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
    StaticKey  key              -> pure $ StaticKey key

-- *** Lens traversals

$(makeTraversals ''NKeyName)


-- ** @NAttrPath@

-- | A selector (for example in a @let@ or an attribute set) is made up
-- of strung-together key names.
--
-- > StaticKey "x" :| [DynamicKey (Antiquoted y)]  ~  x.${y}
type NAttrPath r = NonEmpty (NKeyName r)


-- ** @Binding@

#if !MIN_VERSION_hashable(1,3,1)
-- Required by Hashable Binding deriving. There was none of this Hashable instance before mentioned version, remove this in year >2022
instance Hashable1 NonEmpty
#endif

-- | A single line of the bindings section of a let expression or of a set.
data Binding r
  = NamedVar !(NAttrPath r) !r !SourcePos
  -- ^ An explicit naming.
  --
  -- > NamedVar (StaticKey "x" :| [StaticKey "y"]) z SourcePos{}  ~  x.y = z;
  | Inherit !(Maybe r) ![NKeyName r] !SourcePos
  -- ^ Inheriting an attribute (binding) into the attribute set from the other scope (attribute set). No denoted scope means to inherit from the closest outside scope.
  --
  -- +---------------------------------------------------------------+--------------------+-----------------------+
  -- | Hask                                                          | Nix                | pseudocode            |
  -- +===============================================================+====================+=======================+
  -- | @Inherit Nothing  [StaticKey "a"] SourcePos{}@                | @inherit a;@       | @a = outside.a;@      |
  -- +---------------------------------------------------------------+--------------------+-----------------------+
  -- | @Inherit (pure x) [StaticKey "a"] SourcePos{}@                | @inherit (x) a;@   | @a = x.a;@            |
  -- +---------------------------------------------------------------+--------------------+-----------------------+
  -- | @Inherit (pure x) [StaticKey "a", StaticKey "b"] SourcePos{}@ | @inherit (x) a b;@ | @a = x.a;@            |
  -- |                                                               |                    | @b = x.b;@            |
  -- +---------------------------------------------------------------+--------------------+-----------------------+
  --
  -- (2021-07-07 use details):
  -- Inherits the position of the first name through @unsafeGetAttrPos@. The position of the scope inherited from else - the position of the first member of the binds list.
  deriving
    ( Eq, Ord, Generic, Generic1
    , Typeable, Data, NFData, NFData1, Serialise, Binary, ToJSON, FromJSON
    , Functor, Foldable, Traversable
    , Show, Hashable, Hashable1
    )

$(deriveShow1 ''Binding)
$(deriveEq1   ''Binding)
$(deriveOrd1  ''Binding)
--x $(deriveJSON1 defaultOptions ''Binding)

-- *** Lens traversals

$(makeTraversals ''Binding)


-- ** @Recursivity@

-- | Distinguishes between recursive and non-recursive. Mainly for attribute
-- sets.
data Recursivity
  = NonRecursive  -- ^ >     { ... }
  | Recursive     -- ^ > rec { ... }
  deriving
    ( Eq, Ord, Enum, Bounded, Generic
    , Typeable, Data, NFData, Serialise, Binary, ToJSON, FromJSON
    , Show, Read, Hashable
    )


-- ** @NUnaryOp@

-- | There are two unary operations: logical not and integer negation.
data NUnaryOp
  = NNeg  -- ^ @-@
  | NNot  -- ^ @!@
  deriving
    ( Eq, Ord, Enum, Bounded, Generic
    , Typeable, Data, NFData, Serialise, Binary, ToJSON, FromJSON
    , Show, Read, Hashable
    )

-- *** Lens traversals

$(makeTraversals ''NUnaryOp)


-- ** @NBinaryOp@

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
  | NUpdate  -- ^ Get the left attr set, extend it with the right one & override equal keys (@//@)
  | NPlus    -- ^ Addition (@+@)
  | NMinus   -- ^ Subtraction (@-@)
  | NMult    -- ^ Multiplication (@*@)
  | NDiv     -- ^ Division (@/@)
  | NConcat  -- ^ List concatenation (@++@)
  | NApp     -- ^ Apply a function to an argument.
             --
             -- > NBinary NApp f x  ~  f x
  deriving
    ( Eq, Ord, Enum, Bounded, Generic
    , Typeable, Data, NFData, Serialise, Binary, ToJSON, FromJSON
    , Show, Read, Hashable
    )

-- *** Lens traversals

$(makeTraversals ''NBinaryOp)


-- ** @NExprF@ - Nix expressions, base functor

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
  | NSet !Recursivity ![Binding r]
  -- ^ An attribute set literal
  --
  -- > NSet Recursive    [NamedVar x y _]         ~  rec { x = y; }
  -- > NSet NonRecursive [Inherit Nothing [x] _]  ~  { inherit x; }
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
  | NSelect !(Maybe r) !r !(NAttrPath r)
  --  2021-05-15: NOTE: Default value should be first argument to leverage partial application.
  -- Cascading change diff is not that big.
  -- ^ Dot-reference into an attribute set, optionally providing an
  -- alternative if the key doesn't exist.
  --
  -- > NSelect Nothing  s (x :| [])                ~  s.x
  -- > NSelect (pure y) s (x :| [])                ~  s.x or y
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
  deriving
    ( Eq, Ord, Generic, Generic1
    , Typeable, Data, NFData, NFData1, Serialise, Binary, ToJSON, FromJSON
    , Functor, Foldable, Traversable
    , Show, Hashable, Hashable1
    )


$(deriveShow1 ''NExprF)
$(deriveEq1   ''NExprF)
$(deriveOrd1  ''NExprF)
--x $(deriveJSON1 defaultOptions ''NExprF)

-- *** Lens traversals

$(makeTraversals ''NExprF)


-- *** @NExpr@

-- | The monomorphic expression type is a fixed point of the polymorphic one.
type NExpr = Fix NExprF

-- | We make an `IsString` for expressions, where the string is interpreted
-- as an identifier. This is the most common use-case...
instance IsString NExpr where
  fromString = Fix . NSym . fromString

instance Serialise NExpr

instance TH.Lift NExpr where
  lift =
    TH.dataToExpQ
      (\b ->
        do
          -- Binding on constructor ensures type match and gives type inference to TH.
          -- Reflection is the ability of a process to examine, introspect, and modify its own structure and behavior.
          -- Reflection is a key strategy in metaprogramming.
          -- <https://en.wikipedia.org/wiki/Reflective_programming>
          HRefl <-
            eqTypeRep
              (Reflection.typeRep @Text)
              (Reflection.typeOf  b    )
          pure [| $(TH.lift b) |]
      )
#if MIN_VERSION_template_haskell(2,17,0)
  liftTyped = TH.liftTyped
#elif MIN_VERSION_template_haskell(2,16,0)
  liftTyped = TH.unsafeTExpCoerce . TH.lift
#endif


-- ** Methods

#if __GLASGOW_HASKELL__ >= 900
hashAt
  :: Functor f
  => VarName
  -> (Maybe v -> f (Maybe v))
  -> AttrSet v
  -> f (AttrSet v)
#else
hashAt :: VarName -> Lens' (AttrSet v) (Maybe v)
#endif
hashAt = alterF
 where
  alterF
    :: (Functor f)
    => VarName
    -> (Maybe v -> f (Maybe v))
    -> AttrSet v
    -> f (AttrSet v)
  alterF (coerce -> k) f m =
    maybe
      (MapL.delete k m)
      (\ v -> MapL.insert k v m)
      <$> f (MapL.lookup k m)

-- | Get the name out of the parameter (there might be none).
paramName :: Params r -> Maybe VarName
paramName (Param n       ) = pure n
paramName (ParamSet _ _ n) = n

stripPositionInfo :: NExpr -> NExpr
stripPositionInfo = transport phi
 where
  transport f (Fix x) = Fix $ transport f <$> f x

  phi (NSet recur binds) = NSet recur $ go <$> binds
  phi (NLet binds body) = NLet (go <$> binds) body
  phi x                 = x

  go (NamedVar path r     _pos) = NamedVar path r     nullPos
  go (Inherit  ms   names _pos) = Inherit  ms   names nullPos

nullPos :: SourcePos
nullPos = on (SourcePos "<string>") mkPos 1 1

-- * Dead code

-- ** @class NExprAnn@

class NExprAnn ann g | g -> ann where
  fromNExpr :: g r -> (NExprF r, ann)
  toNExpr :: (NExprF r, ann) -> g r

-- ** Other

ekey
  :: NExprAnn ann g
  => NonEmpty VarName
  -> SourcePos
  -> Lens' (Fix g) (Maybe (Fix g))
ekey keys pos f e@(Fix x) | (NSet NonRecursive xs, ann) <- fromNExpr x =
  case go xs of
    ((v, []      ) : _) -> fromMaybe e <$> f (pure v)
    ((v, r : rest) : _) -> ekey (r :| rest) pos f v

    _                   ->
      maybe
        e
        (\ v ->
          let entry = NamedVar (StaticKey <$> keys) v pos in
          Fix $ toNExpr ( NSet NonRecursive $ [entry] <> xs, ann )
        )
      <$>
        f Nothing
  where
    go xs =
      do
        let keys' = NE.toList keys
        (ks, rest) <- zip (inits keys') (tails keys')
        list
          mempty
          (\ (j : js) ->
            do
              NamedVar ns v _p <- xs
              guard $ (j : js) == (NE.toList ns ^.. traverse . _StaticKey)
              pure (v, rest)
          )
          ks

ekey _ _ f e = fromMaybe e <$> f Nothing
