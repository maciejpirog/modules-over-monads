{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, RankNTypes, DeriveFunctor, GeneralizedNewtypeDeriving #-}

{-|
Module      : Control.Monad.Free.NonPure
Copyright   : (c) 2015 Maciej Piróg
License     : MIT
Maintainer  : maciej.adam.pirog@gmail.com
Stability   : experimental

Generalised resumption monad a la M. Piróg, N. Wu, J. Gibbons
/Modules over monads and their algebras/
<https://coalg.org/calco15/papers/p18-Piróg.pdf>.
-}
module Control.Monad.Free.NonPure
  (
    NonPure(..),
    toNonPure,
    toFree,
    hoistNonPure,
    unfoldNonPure
  )
  where

import Prelude hiding (foldr)
import Control.Monad.Free (Free(..), hoistFree)
import qualified Control.Monad.Free as Free (unfold)
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Data.Functor.Apply (Apply(..))
import Data.Functor.Bind (Bind(..))

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

instance (Functor f, Foldable f) => Foldable (NonPure f) where
  foldMap g f = foldMap g (toFree f)
  foldr g u f = foldr g u (toFree f)

instance (Functor f, Traversable f) => Traversable (NonPure f) where
  sequenceA (NonPure f) = fmap NonPure $ traverse sequenceA f

instance (Functor f) => Apply (NonPure f) where
  NonPure f <.> b = NonPure $ fmap (<.> toFree b) f

instance (Functor f) => Bind (NonPure f) where
  NonPure f >>- h = NonPure $ fmap (>>= toFree . h) f

-- | Transform @'Free'@ to @'NonPure'@. Succeeds only if the
-- argument is indeed non-pure.
toNonPure :: Free f a -> Maybe (NonPure f a)
toNonPure (Pure a) = Nothing
toNonPure (Free f) = Just $ NonPure f

-- | Embedd @'NonPure'@ into @'Free'@.
toFree :: NonPure f a -> Free f a
toFree (NonPure f) = Free f

-- | Lift a natural transformation to \"rename\" the nodes in the
-- structure.
hoistNonPure :: (Functor g) => (forall a. f a -> g a) -> NonPure f a -> NonPure g a
hoistNonPure h (NonPure f) = NonPure $ fmap (hoistFree h) $ h f

-- | Unfold a @'NonPure'@ from a seed @s@.
unfoldNonPure :: (Functor f) => (s -> f (Either a s)) -> s -> NonPure f a
unfoldNonPure h s = NonPure $ fmap (Free.unfold $ fmap h) $ h s
