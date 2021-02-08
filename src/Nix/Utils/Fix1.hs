{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Nix.Utils.Fix1 where

import           Control.Applicative            ( Alternative )
#if !MIN_VERSION_base(4,13,0)
import           Control.Monad.Fail
#endif
import           Control.Monad                  ( MonadPlus )
import           Control.Monad.Fix              ( MonadFix )
import           Control.Monad.IO.Class         ( MonadIO )
import           Control.Monad.Catch            ( MonadCatch
                                                , MonadMask
                                                , MonadThrow )
import           Control.Monad.Reader           ( MonadReader )
import           Control.Monad.State            ( MonadState )

import Nix.Thunk --TODO: Move MonadTransWrap somewhere better, or find something that already exists

-- | The fixpoint combinator, courtesy of Gregory Malecha.
--   https://gist.github.com/gmalecha/ceb3778b9fdaa4374976e325ac8feced
newtype Fix1 (t :: (k -> *) -> k -> *) (a :: k) = Fix1 { unFix1 :: t (Fix1 t) a }

deriving instance Functor (t (Fix1 t)) => Functor (Fix1 t)
deriving instance Applicative (t (Fix1 t)) => Applicative (Fix1 t)
deriving instance Alternative (t (Fix1 t)) => Alternative (Fix1 t)
deriving instance Monad (t (Fix1 t)) => Monad (Fix1 t)
deriving instance MonadPlus (t (Fix1 t)) => MonadPlus (Fix1 t)
deriving instance MonadFix (t (Fix1 t)) => MonadFix (Fix1 t)
deriving instance MonadIO (t (Fix1 t)) => MonadIO (Fix1 t)
deriving instance MonadCatch (t (Fix1 t)) => MonadCatch (Fix1 t)
deriving instance MonadThrow (t (Fix1 t)) => MonadThrow (Fix1 t)

deriving instance MonadReader e (t (Fix1 t)) => MonadReader e (Fix1 t)
deriving instance MonadState s (t (Fix1 t)) => MonadState s (Fix1 t)

newtype Fix1T (t :: (k -> *) -> (* -> *) -> k -> *) (m :: * -> *) (a :: k)
  = Fix1T { unFix1T :: t (Fix1T t m) m a }

deriving instance Functor (t (Fix1T t m) m) => Functor (Fix1T t m)
deriving instance Applicative (t (Fix1T t m) m) => Applicative (Fix1T t m)
deriving instance Alternative (t (Fix1T t m) m) => Alternative (Fix1T t m)
deriving instance Monad (t (Fix1T t m) m) => Monad (Fix1T t m)
deriving instance MonadFail (t (Fix1T t m) m) => MonadFail (Fix1T t m)
deriving instance MonadPlus (t (Fix1T t m) m) => MonadPlus (Fix1T t m)
deriving instance MonadFix (t (Fix1T t m) m) => MonadFix (Fix1T t m)
deriving instance MonadIO (t (Fix1T t m) m) => MonadIO (Fix1T t m)
deriving instance MonadCatch (t (Fix1T t m) m) => MonadCatch (Fix1T t m)
deriving instance MonadThrow (t (Fix1T t m) m) => MonadThrow (Fix1T t m)
deriving instance MonadMask (t (Fix1T t m) m) => MonadMask (Fix1T t m)

deriving instance MonadReader e (t (Fix1T t m) m) => MonadReader e (Fix1T t m)
deriving instance MonadState s (t (Fix1T t m) m) => MonadState s (Fix1T t m)

instance (forall m. MonadTransWrap (t (Fix1T t m))) => MonadTransWrap (Fix1T t) where
  liftWrap f (Fix1T a) = Fix1T $ liftWrap f a

{-

newtype Flip (f :: i -> j -> *) (a :: j) (b :: i) = Flip { unFlip :: f b a }

-- | Natural Transformations (Included from
--   [compdata](https://hackage.haskell.org/package/compdata))
type (:->) f g = forall a. f a -> g a

class HFunctor f where
  hfmap :: a :-> b -> f a :-> f b

-}
