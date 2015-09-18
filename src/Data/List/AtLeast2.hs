{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, DeriveFunctor #-}

{-|
Module      : Data.List.AtLeast2
Copyright   : (c) 2015 Maciej Piróg
License     : MIT
Maintainer  : maciej.adam.pirog@gmail.com
Stability   : experimental


Lists with at least 2 elements. They do not form a monad (no way to
define @'return'@), but they form a @'Bind'@. Moreover, they are
the ideal that idealises non-empty lists.
-}

module Data.List.AtLeast2
  (
    AtLeast2(..),
    toList,
    toNonEmpty
  )
  where

import Prelude hiding (foldr)
import Control.Applicative (Applicative(..), (<$>))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Data.Functor.Apply (Apply(..))
import Data.Functor.Bind (Bind(..))

import Control.Monad.Module

{- | List with at least two elements -}
data AtLeast2 a = a :|: NonEmpty a
 deriving (Eq, Ord, Show, Read, Functor)

infixr 4 :|:

toList :: AtLeast2 a -> [a]
toList (x :|: y :| xs) = x : y : xs

instance Foldable AtLeast2 where
  foldr f a = foldr f a . toList

instance Traversable AtLeast2 where
  traverse h (x :|: xs) = (:|:) <$> h x <*> traverse h xs

instance Apply AtLeast2 where
  (f :|: g :| fs) <.> (x :|: y :| xs) =
    f x :|: f y :| fmap f xs ++ (g : fs <.> x : y : xs)

instance Bind AtLeast2 where
  x :|: y :| z >>- h = t :|: v :| ts ++ ((y : z) >>- (toList . h))
   where
    t :|: v :| ts = h x

fromNonEmpty :: NonEmpty a -> AtLeast2 a
fromNonEmpty (x :| y : xs) = x :|: y :| xs

toNonEmpty :: AtLeast2 a -> NonEmpty a
toNonEmpty (x :|: y :| xs) = x :| y : xs

instance RModule NonEmpty AtLeast2 where
  m |>>= f = fromNonEmpty $ toNonEmpty m >>= f

instance Idealised NonEmpty AtLeast2 where
  embed = toNonEmpty

instance MonadIdeal NonEmpty where
  type Ideal NonEmpty = AtLeast2
  split (x :| []) = Left x
  split xs        = Right $ fromNonEmpty xs
