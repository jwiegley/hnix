{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}

module Nix.Value where

import           Control.Comonad                ( Comonad, extract )
import           Control.Exception              ( Exception )
import           Control.Monad                  ( (<=<) )
import           Control.Monad.Free             ( Free(..)
                                                , hoistFree, iter, iterM )
import           Control.Monad.Trans.Class      ( MonadTrans, lift )
import qualified Data.Aeson                    as A
import           Data.Functor.Classes           ( Show1
                                                , liftShowsPrec
                                                , showsUnaryWith )
import           Data.HashMap.Lazy              ( HashMap )
import           Data.Text                      ( Text )
import           Data.Typeable                  ( Typeable )
import           GHC.Generics                   ( Generic )
import           Lens.Family2.Stock             ( _1 )
import           Lens.Family2.TH                ( makeTraversals
                                                , makeLenses )
import           Nix.Atoms
import           Nix.Expr.Types
import           Nix.Expr.Types.Annotated
import           Nix.String
import           Nix.Thunk
import           Nix.Utils

-- | 'NValue' is the most reduced form of a 'NExpr' after evaluation is
--   completed. 's' is related to the type of errors that might occur during
--   construction or use of a value.
data NValueF p m r
    = NVConstantF NAtom
     -- | A string has a value and a context, which can be used to record what a
     -- string has been build from
    | NVStrF NixString
    | NVPathF FilePath
    | NVListF [r]
    | NVSetF (AttrSet r) (AttrSet SourcePos)
    | NVClosureF (Params ()) (p -> m r)
      -- ^ A function is a closed set of parameters representing the "call
      --   signature", used at application time to check the type of arguments
      --   passed to the function. Since it supports default values which may
      --   depend on other values within the final argument set, this
      --   dependency is represented as a set of pending evaluations. The
      --   arguments are finally normalized into a set which is passed to the
      --   function.
      --
      --   Note that 'm r' is being used here because effectively a function
      --   and its set of default arguments is "never fully evaluated". This
      --   enforces in the type that it must be re-evaluated for each call.
    | NVBuiltinF VarName (p -> m r)
      -- ^ A builtin function is itself already in normal form. Also, it may
      --   or may not choose to evaluate its argument in the production of a
      --   result.
    deriving (Generic, Typeable, Functor)

-- | Folds what the value is known to contain at time of fold.
instance Foldable (NValueF p m) where
  foldMap f = \case
    NVConstantF _  -> mempty
    NVStrF      _  -> mempty
    NVPathF     _  -> mempty
    NVListF     l  -> foldMap f l
    NVSetF     s _ -> foldMap f s
    NVClosureF _ _ -> mempty
    NVBuiltinF _ _ -> mempty

instance Show r => Show (NValueF p m r) where
  showsPrec = flip go   where
    go (NVConstantF atom  ) = showsCon1 "NVConstant" atom
    go (NVStrF      ns    ) = showsCon1 "NVStr" (stringIgnoreContext ns)
    go (NVListF     lst   ) = showsCon1 "NVList" lst
    go (NVSetF     attrs _) = showsCon1 "NVSet" attrs
    go (NVClosureF p     _) = showsCon1 "NVClosure" p
    go (NVPathF p         ) = showsCon1 "NVPath" p
    go (NVBuiltinF name _ ) = showsCon1 "NVBuiltin" name

    showsCon1 :: Show a => String -> a -> Int -> String -> String
    showsCon1 con a d =
      showParen (d > 10) $ showString (con ++ " ") . showsPrec 11 a

lmapNValueF :: Functor m => (b -> a) -> NValueF a m r -> NValueF b m r
lmapNValueF f = \case
  NVConstantF a  -> NVConstantF a
  NVStrF      s  -> NVStrF s
  NVPathF     p  -> NVPathF p
  NVListF     l  -> NVListF l
  NVSetF     s p -> NVSetF s p
  NVClosureF p g -> NVClosureF p (g . f)
  NVBuiltinF s g -> NVBuiltinF s (g . f)

hoistNValueF
  :: (forall x . m x -> n x)
  -> NValueF p m a
  -> NValueF p n a
hoistNValueF lft = \case
  NVConstantF a  -> NVConstantF a
  NVStrF      s  -> NVStrF s
  NVPathF     p  -> NVPathF p
  NVListF     l  -> NVListF l
  NVSetF     s p -> NVSetF s p
  NVClosureF p g -> NVClosureF p (lft . g)
  NVBuiltinF s g -> NVBuiltinF s (lft . g)

sequenceNValueF
  :: (Functor n, Monad m, Applicative n)
  => (forall x . n x -> m x)
  -> NValueF p m (n a)
  -> n (NValueF p m a)
sequenceNValueF transform = \case
  NVConstantF a  -> pure $ NVConstantF a
  NVStrF      s  -> pure $ NVStrF s
  NVPathF     p  -> pure $ NVPathF p
  NVListF     l  -> NVListF <$> sequenceA l
  NVSetF     s p -> NVSetF <$> sequenceA s <*> pure p
  NVClosureF p g -> pure $ NVClosureF p (transform <=< g)
  NVBuiltinF s g -> pure $ NVBuiltinF s (transform <=< g)

bindNValueF
  :: (Monad m, Monad n)
  => (forall x . n x -> m x)
  -> (a -> n b)
  -> NValueF p m a
  -> n (NValueF p m b)
bindNValueF transform f = \case
  NVConstantF a  -> pure $ NVConstantF a
  NVStrF      s  -> pure $ NVStrF s
  NVPathF     p  -> pure $ NVPathF p
  NVListF     l  -> NVListF <$> traverse f l
  NVSetF     s p -> NVSetF <$> traverse f s <*> pure p
  NVClosureF p g -> pure $ NVClosureF p (transform . f <=< g)
  NVBuiltinF s g -> pure $ NVBuiltinF s (transform . f <=< g)

liftNValueF
  :: (MonadTrans u, Monad m)
  => NValueF p m a
  -> NValueF p (u m) a
liftNValueF = hoistNValueF lift

unliftNValueF
  :: (MonadTrans u, Monad m)
  => (forall x . u m x -> m x)
  -> NValueF p (u m) a
  -> NValueF p m a
unliftNValueF = hoistNValueF

type MonadDataContext f (m :: * -> *)
  = (Comonad f, Applicative f, Traversable f, Monad m)

-- | At the time of constructor, the expected arguments to closures are values
--   that may contain thunks. The type of such thunks are fixed at that time.
newtype NValue' t f m a = NValue { _nValue :: f (NValueF (NValue t f m) m a) }
    deriving (Generic, Typeable, Functor, Foldable)

instance (Comonad f, Show a) => Show (NValue' t f m a) where
  show (NValue (extract -> v)) = show v

instance Comonad f => Show1 (NValue' t f m) where
  liftShowsPrec sp sl p = \case
    NVConstant' atom  -> showsUnaryWith showsPrec "NVConstantF" p atom
    NVStr' ns ->
      showsUnaryWith showsPrec "NVStrF" p (stringIgnoreContext ns)
    NVList' lst       -> showsUnaryWith (liftShowsPrec sp sl) "NVListF" p lst
    NVSet' attrs _    -> showsUnaryWith (liftShowsPrec sp sl) "NVSetF" p attrs
    NVPath' path      -> showsUnaryWith showsPrec "NVPathF" p path
    NVClosure' c    _ -> showsUnaryWith showsPrec "NVClosureF" p c
    NVBuiltin' name _ -> showsUnaryWith showsPrec "NVBuiltinF" p name
    _                 -> error "Pattern synonyms mask coverage"

sequenceNValue'
  :: (Functor n, Traversable f, Monad m, Applicative n)
  => (forall x . n x -> m x)
  -> NValue' t f m (n a)
  -> n (NValue' t f m a)
sequenceNValue' transform (NValue v) =
  NValue <$> traverse (sequenceNValueF transform) v

bindNValue'
  :: (Traversable f, Monad m, Monad n)
  => (forall x . n x -> m x)
  -> (a -> n b)
  -> NValue' t f m a
  -> n (NValue' t f m b)
bindNValue' transform f (NValue v) =
  NValue <$> traverse (bindNValueF transform f) v

hoistNValue'
  :: (Functor m, Functor n, Functor f)
  => (forall x . n x -> m x)
  -> (forall x . m x -> n x)
  -> NValue' t f m a
  -> NValue' t f n a
hoistNValue' run lft (NValue v) =
    NValue (fmap (lmapNValueF (hoistNValue lft run) . hoistNValueF lft) v)

liftNValue'
  :: (MonadTrans u, Monad m, Functor (u m), Functor f)
  => (forall x . u m x -> m x)
  -> NValue' t f m a
  -> NValue' t f (u m) a
liftNValue' run = hoistNValue' run lift

unliftNValue'
  :: (MonadTrans u, Monad m, Functor (u m), Functor f)
  => (forall x . u m x -> m x)
  -> NValue' t f (u m) a
  -> NValue' t f m a
unliftNValue' run = hoistNValue' lift run

iterNValue'
  :: forall t f m a r
   . MonadDataContext f m
  => (a -> (NValue' t f m a -> r) -> r)
  -> (NValue' t f m r -> r)
  -> NValue' t f m a
  -> r
iterNValue' k f = f . fmap (\a -> k a (iterNValue' k f))

-- | A 'NValue t f m' is
--   a value in head normal form, where only the "top layer" has been
--   evaluated. An action of type 'm (NValue t f m)' is a pending evaluation that
--   has yet to be performed. An 't' is either a pending evaluation, or
--   a value in head normal form.
--
--   The 'Free' structure is used here to represent the possibility that
--   cycles may appear during normalization.

type NValue t f m = Free (NValue' t f m) t

hoistNValue
  :: (Functor m, Functor n, Functor f)
  => (forall x . n x -> m x)
  -> (forall x . m x -> n x)
  -> NValue t f m
  -> NValue t f n
hoistNValue run lft = hoistFree (hoistNValue' run lft)

liftNValue
  :: (MonadTrans u, Monad m, Functor (u m), Functor f)
  => (forall x . u m x -> m x)
  -> NValue t f m
  -> NValue t f (u m)
liftNValue run = hoistNValue run lift

unliftNValue
  :: (MonadTrans u, Monad m, Functor (u m), Functor f)
  => (forall x . u m x -> m x)
  -> NValue t f (u m)
  -> NValue t f m
unliftNValue run = hoistNValue lift run

iterNValue
  :: forall t f m r
   . MonadDataContext f m
  => (t -> (NValue t f m -> r) -> r)
  -> (NValue' t f m r -> r)
  -> NValue t f m
  -> r
iterNValue k f = iter f . fmap (\t -> k t (iterNValue k f))

iterNValueM
  :: (MonadDataContext f m, Monad n)
  => (forall x . n x -> m x)
  -> (t -> (NValue t f m -> n r) -> n r)
  -> (NValue' t f m (n r) -> n r)
  -> NValue t f m
  -> n r
iterNValueM transform k f =
    iterM f <=< go . fmap (\t -> k t (iterNValueM transform k f))
  where
    go (Pure x) = Pure <$> x
    go (Free fa) = Free <$> bindNValue' transform go fa

pattern NVThunk t <- Pure t

nvThunk :: Applicative f => t -> NValue t f m
nvThunk = Pure

pattern NVConstant' x <- NValue (extract -> NVConstantF x)
pattern NVConstant x <- Free (NVConstant' x)

nvConstant' :: Applicative f => NAtom -> NValue' t f m r
nvConstant' = NValue . pure . NVConstantF
nvConstant :: Applicative f => NAtom -> NValue t f m
nvConstant = Free . nvConstant'

pattern NVStr' ns <- NValue (extract -> NVStrF ns)
pattern NVStr ns <- Free (NVStr' ns)

nvStr' :: Applicative f => NixString -> NValue' t f m r
nvStr' = NValue . pure . NVStrF
nvStr :: Applicative f => NixString -> NValue t f m
nvStr = Free . nvStr'

pattern NVPath' x <- NValue (extract -> NVPathF x)
pattern NVPath x <- Free (NVPath' x)

nvPath' :: Applicative f => FilePath -> NValue' t f m r
nvPath' = NValue . pure . NVPathF
nvPath :: Applicative f => FilePath -> NValue t f m
nvPath = Free . nvPath'

pattern NVList' l <- NValue (extract -> NVListF l)
pattern NVList l <- Free (NVList' l)

nvList' :: Applicative f => [r] -> NValue' t f m r
nvList' = NValue . pure . NVListF
nvList :: Applicative f => [NValue t f m] -> NValue t f m
nvList = Free . nvList'

pattern NVSet' s x <- NValue (extract -> NVSetF s x)
pattern NVSet s x <- Free (NVSet' s x)

nvSet' :: Applicative f
       => HashMap VarName r -> HashMap VarName SourcePos -> NValue' t f m r
nvSet' s x = NValue $ pure $ NVSetF s x
nvSet :: Applicative f
      => HashMap VarName (NValue t f m) -> HashMap VarName SourcePos -> NValue t f m
nvSet s x = Free $ nvSet' s x

pattern NVClosure' x f <- NValue (extract -> NVClosureF x f)
pattern NVClosure x f <- Free (NVClosure' x f)

nvClosure' :: (Applicative f, Functor m)
           => Params () -> (NValue t f m -> m r) -> NValue' t f m r
nvClosure' x f = NValue $ pure $ NVClosureF x f
nvClosure :: (Applicative f, Functor m)
          => Params () -> (NValue t f m -> m (NValue t f m)) -> NValue t f m
nvClosure x f = Free $ nvClosure' x f

pattern NVBuiltin' name f <- NValue (extract -> NVBuiltinF name f)
pattern NVBuiltin name f <- Free (NVBuiltin' name f)

nvBuiltin' :: (Applicative f, Functor m)
           => VarName -> (NValue t f m -> m r) -> NValue' t f m r
nvBuiltin' name f = NValue $ pure $ NVBuiltinF name f
nvBuiltin :: (Applicative f, Functor m)
          => VarName -> (NValue t f m -> m (NValue t f m)) -> NValue t f m
nvBuiltin name f = Free $ nvBuiltin' name f

builtin
  :: forall m f t
   . (MonadThunk t m (NValue t f m), MonadDataContext f m)
  => VarName
  -> (NValue t f m -> m (NValue t f m))
  -> m (NValue t f m)
builtin name f = pure $ nvBuiltin name $ \a -> f a

builtin2
  :: (MonadThunk t m (NValue t f m), MonadDataContext f m)
  => VarName
  -> (NValue t f m -> NValue t f m -> m (NValue t f m))
  -> m (NValue t f m)
builtin2 name f = builtin name $ \a -> builtin name $ \b -> f a b

builtin3
  :: (MonadThunk t m (NValue t f m), MonadDataContext f m)
  => VarName
  -> (  NValue t f m
     -> NValue t f m
     -> NValue t f m
     -> m (NValue t f m)
     )
  -> m (NValue t f m)
builtin3 name f =
  builtin name $ \a -> builtin name $ \b -> builtin name $ \c -> f a b c

data TStringContext = NoContext | HasContext
  deriving Show

data ValueType
    = TInt
    | TFloat
    | TBool
    | TNull
    | TString TStringContext
    | TList
    | TSet
    | TClosure
    | TPath
    | TBuiltin
    deriving Show

valueType :: NValueF a m r -> ValueType
valueType = \case
  NVConstantF a -> case a of
    NURI   _ -> TString NoContext
    NInt   _ -> TInt
    NFloat _ -> TFloat
    NBool  _ -> TBool
    NNull    -> TNull
  NVStrF ns | stringHasContext ns -> TString HasContext
            | otherwise           -> TString NoContext
  NVListF{}    -> TList
  NVSetF{}     -> TSet
  NVClosureF{} -> TClosure
  NVPathF{}    -> TPath
  NVBuiltinF{} -> TBuiltin

describeValue :: ValueType -> String
describeValue = \case
  TInt               -> "an integer"
  TFloat             -> "a float"
  TBool              -> "a boolean"
  TNull              -> "a null"
  TString NoContext  -> "a string"
  TString HasContext -> "a string with context"
  TList              -> "a list"
  TSet               -> "an attr set"
  TClosure           -> "a function"
  TPath              -> "a path"
  TBuiltin           -> "a builtin function"

showValueType :: (MonadThunk t m (NValue t f m), Comonad f)
              => NValue t f m -> m String
showValueType (Pure t) = force t showValueType
showValueType (Free (NValue (extract -> v))) =
  pure $ describeValue $ valueType v

data ValueFrame t f m
    = ForcingThunk t
    | ConcerningValue (NValue t f m)
    | Comparison (NValue t f m) (NValue t f m)
    | Addition (NValue t f m) (NValue t f m)
    | Multiplication (NValue t f m) (NValue t f m)
    | Division (NValue t f m) (NValue t f m)
    | Coercion ValueType ValueType
    | CoercionToJson (NValue t f m)
    | CoercionFromJson A.Value
    | Expectation ValueType (NValue t f m)
    deriving Typeable

deriving instance (Comonad f, Show t) => Show (ValueFrame t f m)

type MonadDataErrorContext t f m
  = (Show t, Typeable t, Typeable m, Typeable f, MonadDataContext f m)

instance MonadDataErrorContext t f m => Exception (ValueFrame t f m)

$(makeTraversals ''NValueF)
$(makeLenses ''NValue')

key
  :: (Traversable f, Applicative g)
  => VarName
  -> LensLike' g (NValue' t f m a) (Maybe a)
key k = nValue . traverse . _NVSetF . _1 . hashAt k
