{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Nix.Utils (module Nix.Utils, module X) where

import qualified Codec.Serialise
import           Control.Arrow                  ( (&&&) )
import           Control.DeepSeq
import           Control.Monad                  ( (<=<) )
import           Control.Monad.Fix              ( MonadFix(..) )
import           Control.Monad.Free             ( Free(..) )
import           Control.Monad.Trans.Control    ( MonadTransControl(..) )
import qualified Data.Aeson                    as A
import qualified Data.Aeson.Encoding           as A
import qualified Data.Binary
import           Data.Data
import           Data.Fix                       ( Fix(..) )
import           Data.Hashable                  ( Hashable )
import           Data.HashMap.Lazy              ( HashMap )
import qualified Data.HashMap.Lazy             as M
import           Data.Interned.Text
import           Data.Interned
import           Data.List                      ( sortOn )
import           Data.Monoid                    ( Endo )
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import qualified Data.Vector                   as V
import           GHC.Generics                   ( Generic )
import           Lens.Family2                  as X
import           Lens.Family2.Stock             ( _1
                                                , _2
                                                )
import           Lens.Family2.TH                ( makeLensesBy )

#if ENABLE_TRACING
import           Debug.Trace as X
#else
import           Prelude                       as X
                                         hiding ( putStr
                                                , putStrLn
                                                , print
                                                )
trace :: String -> a -> a
trace = const id
traceM :: Monad m => String -> m ()
traceM = const (pure ())
#endif

$(makeLensesBy (\n -> Just ("_" ++ n)) ''Fix)

type DList a = Endo [a]

type AttrSet = HashMap VarName

-- | F-algebra defines how to reduce the fixed-point of a functor to a
--   value.
type Alg f a = f a -> a

type AlgM f m a = f a -> m a

-- | "Transform" here means a modification of a catamorphism.
type Transform f a = (Fix f -> a) -> Fix f -> a

(<&>) :: Functor f => f a -> (a -> c) -> f c
(<&>) = flip (<$>)

(??) :: Functor f => f (a -> b) -> a -> f b
fab ?? a = fmap ($ a) fab

loeb :: Functor f => f (f a -> a) -> f a
loeb x = go where go = fmap ($ go) x

loebM :: (MonadFix m, Traversable t) => t (t a -> m a) -> m (t a)
loebM f = mfix $ \a -> mapM ($ a) f

para :: Functor f => (f (Fix f, a) -> a) -> Fix f -> a
para f = f . fmap (id &&& para f) . unFix

paraM :: (Traversable f, Monad m) => (f (Fix f, a) -> m a) -> Fix f -> m a
paraM f = f <=< traverse (\x -> (x, ) <$> paraM f x) . unFix

cataP :: Functor f => (Fix f -> f a -> a) -> Fix f -> a
cataP f x = f x . fmap (cataP f) . unFix $ x

cataPM :: (Traversable f, Monad m) => (Fix f -> f a -> m a) -> Fix f -> m a
cataPM f x = f x <=< traverse (cataPM f) . unFix $ x

transport :: Functor g => (forall x . f x -> g x) -> Fix f -> Fix g
transport f (Fix x) = Fix $ fmap (transport f) (f x)

lifted
  :: (MonadTransControl u, Monad (u m), Monad m)
  => ((a -> m (StT u b)) -> m (StT u b))
  -> (a -> u m b)
  -> u m b
lifted f k = liftWith (\run -> f (run . k)) >>= restoreT . pure

freeToFix :: Functor f => (a -> Fix f) -> Free f a -> Fix f
freeToFix f = go
 where
  go (Pure a) = f a
  go (Free v) = Fix (fmap go v)

fixToFree :: Functor f => Fix f -> Free f a
fixToFree = Free . go where go (Fix f) = fmap (Free . go) f

-- | adi is Abstracting Definitional Interpreters:
--
--     https://arxiv.org/abs/1707.04755
--
--   Essentially, it does for evaluation what recursion schemes do for
--   representation: allows threading layers through existing structure, only
--   in this case through behavior.
adi :: Functor f => (f a -> a) -> ((Fix f -> a) -> Fix f -> a) -> Fix f -> a
adi f g = g (f . fmap (adi f g) . unFix)

adiM
  :: (Traversable t, Monad m)
  => (t a -> m a)
  -> ((Fix t -> m a) -> Fix t -> m a)
  -> Fix t
  -> m a
adiM f g = g ((f <=< traverse (adiM f g)) . unFix)

class Has a b where
    hasLens :: Lens' a b

instance Has a a where
  hasLens f = f

instance Has (a, b) a where
  hasLens = _1

instance Has (a, b) b where
  hasLens = _2

toEncodingSorted :: A.Value -> A.Encoding
toEncodingSorted = \case
  A.Object m ->
    A.pairs
      . mconcat
      . fmap (\(k, v) -> A.pair k $ toEncodingSorted v)
      . sortOn fst
      $ M.toList m
  A.Array l -> A.list toEncodingSorted $ V.toList l
  v         -> A.toEncoding v

data NixPathEntryType = PathEntryPath | PathEntryURI deriving (Show, Eq)

-- | @NIX_PATH@ is colon-separated, but can also contain URLs, which have a colon
-- (i.e. @https://...@)
uriAwareSplit :: Text -> [(Text, NixPathEntryType)]
uriAwareSplit = go where
  go str = case Text.break (== ':') str of
    (e1, e2)
      | Text.null e2
      -> [(e1, PathEntryPath)]
      | Text.pack "://" `Text.isPrefixOf` e2
      -> let ((suffix, _) : path) = go (Text.drop 3 e2)
         in  (e1 <> Text.pack "://" <> suffix, PathEntryURI) : path
      | otherwise
      -> (e1, PathEntryPath) : go (Text.drop 1 e2)

alterF
  :: (Eq k, Hashable k, Functor f)
  => (Maybe v -> f (Maybe v))
  -> k
  -> HashMap k v
  -> f (HashMap k v)
alterF f k m = f (M.lookup k m) <&> \case
  Nothing -> M.delete k m
  Just v  -> M.insert k v m


type VarName = InternedText

instance Read VarName where
  readsPrec i v = (\(t, s) -> (intern t, s)) <$> readsPrec i v


internConstr :: Constr
internConstr = mkConstr internedTextDataType "intern" [] Prefix

internedTextDataType :: DataType
internedTextDataType = mkDataType "Data.Interned" [internConstr]

instance Data VarName where
  gfoldl f z v = z intern `f` (unintern v)
  toConstr _ = internConstr
  gunfold k z c = case constrIndex c of
    1 -> k (z intern)
    _ -> error "gunfold"
  dataTypeOf _ = internedTextDataType 
  
instance NFData InternedText where rnf !_ = ()

instance Data.Binary.Binary InternedText where 
  put = Data.Binary.put . unintern
  get = intern <$> Data.Binary.get

-- instance Generic InternedText where

instance Codec.Serialise.Serialise InternedText where
  encode =  Codec.Serialise.encode . unintern
  decode = intern <$>  Codec.Serialise.decode @Text


-- derive instance Data VarName
