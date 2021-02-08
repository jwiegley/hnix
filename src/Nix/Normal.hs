{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Code for normalization (reduction into a normal form) of Nix expressions.
-- Nix language allows recursion, so some expressions do not converge.
-- And so do not converge into a normal form.
module Nix.Normal where

import           Control.Comonad
import           Control.Monad
import           Control.Monad.Free
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Reader
import           Control.Monad.Trans.State
import           Data.Set
import           Nix.Cited
import           Nix.Frames
import           Nix.String
import           Nix.Thunk
import           Nix.Value
import           Nix.Utils

newtype NormalLoop f m = NormalLoop (NValue f m)

deriving instance (Comonad f, Show (Thunk m)) => Show (NormalLoop f m)

instance MonadDataErrorContext f m => Exception (NormalLoop f m)

-- | Normalize the value as much as possible, leaving only detected cycles.
normalizeValue
  :: forall e t m f
   . ( Framed e m
     , MonadThunk m, Thunk m ~ t, ThunkValue m ~ NValue f m
     , MonadDataErrorContext f m
     , Ord (Thunk m)
     )
  => (forall r . t -> (NValue f m -> m r) -> m r)
  -> NValue f m
  -> m (NValue f m)
normalizeValue f = run . iterNValueM run go (fmap Free . sequenceNValue' run)
 where
  start = 0 :: Int
  table = mempty

  run :: ReaderT Int (StateT (Set (Thunk m)) m) r -> m r
  run = (`evalStateT` table) . (`runReaderT` start)

  go
    :: t
    -> (  NValue f m
       -> ReaderT Int (StateT (Set (Thunk m)) m) (NValue f m)
       )
    -> ReaderT Int (StateT (Set (Thunk m)) m) (NValue f m)
  go t k = do
    b <- seen t
    if b
      then pure $ Pure t
      else do
        i <- ask
        when (i > 2000)
          $ error "Exceeded maximum normalization depth of 2000 levels"
        lifted (lifted (f t)) $ local succ . k

  seen t = do
    lift $ do
      res <- gets (member t)
      unless res $ modify (insert t)
      pure res

normalForm
  :: ( Framed e m
     , MonadThunk m, ThunkValue m ~ NValue f m
     , MonadDataErrorContext f m
     , HasCitations m (NValue f m) (Thunk m)
     , HasCitations1 m (NValue f m) f
     , Ord (Thunk m)
     )
  => NValue f m
  -> m (NValue f m)
normalForm = fmap stubCycles . normalizeValue force

normalForm_
  :: ( Framed e m
     , MonadThunk m, ThunkValue m ~ NValue f m
     , MonadDataErrorContext f m
     , Ord (Thunk m)
     )
  => NValue f m
  -> m ()
normalForm_ = void <$> normalizeValue forceEff

stubCycles
  :: forall f m
   . ( MonadDataContext f m
     , HasCitations m (NValue f m) (Thunk m)
     , HasCitations1 m (NValue f m) f
     )
  => NValue f m
  -> NValue f m
stubCycles = flip iterNValue Free $ \t _ ->
  Free
    $ NValue
    $ Prelude.foldr (addProvenance1 @m @(NValue f m)) cyc
    $ reverse
    $ citations @m @(NValue f m) t
 where
  Free (NValue cyc) = opaque

removeEffects
  :: (MonadThunk m, ThunkValue m ~ NValue f m, MonadDataContext f m)
  => NValue f m
  -> m (NValue f m)
removeEffects =
  iterNValueM
    id
    (`queryM` pure opaque)
    (fmap Free . sequenceNValue' id)

opaque :: Applicative f => NValue f m
opaque = nvStr $ makeNixStringWithoutContext "<expr>"

dethunk
  :: (MonadThunk m, Thunk m ~ t, ThunkValue m ~ NValue f m, MonadDataContext f m)
  => t
  -> m (NValue f m)
dethunk t = queryM t (pure opaque) removeEffects
