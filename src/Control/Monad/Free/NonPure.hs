{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, DeriveFunctor, GeneralizedNewtypeDeriving #-}

module Control.Monad.Free.NonPure
  (
    NonPure(..),
    toNonPure,
    toFree,
    unfold
  )
  where

import Control.Monad.Free (Free(..))
import qualified Control.Monad.Free as Free (unfold)

import Control.Monad.Module

-- | Type of \"free monads\" with at least one level of structure.
newtype NonPure f a = NonPure { unNonPure :: f (Free f a) }
 deriving(Functor)

instance (Functor f) => RModule (Free f) (NonPure f) where
  (NonPure f) |>>= g = NonPure (fmap (>>= g) f)

instance (Functor f) => Idealised (Free f) (NonPure f) where
  embed = Free . unNonPure

instance (Functor f) => MonadIdeal (Free f) where
  type Ideal (Free f) = NonPure f
  split (Pure x) = Left x
  split (Free f) = Right $ NonPure f

-- | Transform @'Free'@ to @'NonPure'@. Suceeds only if the
-- argument is indeed non-pure.
toNonPure :: Free f a -> Maybe (NonPure f a)
toNonPure (Pure a) = Nothing
toNonPure (Free f) = Just $ NonPure f

-- | Embedd @'NonPure'@ into @'Free'@.
toFree :: NonPure f a -> Free f a
toFree (NonPure f) = Free f

-- | Unfolds a @'NonPure'@ from a seed @s@.
unfold :: (Functor f) => (s -> f (Either a s)) -> s -> NonPure f a
unfold h s = NonPure $ fmap (Free.unfold $ fmap h) $ h s
  
