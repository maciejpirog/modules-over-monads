{-# LANGUAGE TypeFamilies, FlexibleInstances, DeriveFunctor #-}

{-|
Module      : Resumption
Description : Ideal monoids (semigroups with freely adjoined unit)
Copyright   : (c) Maciej Piróg
License     : MIT
Maintainer  : maciej.adam.pirog@gmail.com
Stability   : experimental

Class of ideal monoids (that is, monoids that are semigroups with
freely adjoined unit).
-}

module MonoidIdeal
  (
    -- * @'MonoidIdeal'@ typeclass
    MonoidIdeal(..),
    -- * Products of ideal monoids
    MaybeProduct(..),
    -- * Additional functions
    isUnit
  )
  where

import Data.Monoid
import Data.Word
import Data.Void
import Data.List.NonEmpty
import Data.Maybe (fromJust)

class (Monoid r) => MonoidIdeal r where

  -- | Type of elements of the semigroup.
  type MIdeal r :: *

  -- | Check if the argument is the adjoined unit (@Nothing@) or
  -- an element of the semigroup @r@ (@Just x@).
  misplit :: r -> Maybe (MIdeal r)

  -- | Embed the semigroup @MIdeal r@ in the monoid. The adjoined
  -- unit (that is, the value @Nothing@) goes to the unit of the
  -- monoid.
  mifuse  :: Maybe (MIdeal r) -> r
  mifuse Nothing  = mempty
  mifuse (Just a) = miembed a
  
  -- | Embed the semigroup in the monoid.
  miembed :: MIdeal r -> r
  miembed = mifuse . Just

  -- | The semigroup @MIdeal r@ is a right ideal of @r@.
  --
  -- Note that we could altenratively try to use the multiplication
  -- of the semigroup
  --
  -- * @'miappend' :: 'MIdeal' r -> 'MIdeal' r -> 'MIdeal' r@
  --
  -- but this would lead to ambiguity in type-checking, as 'MIdeal'
  -- is not necessarily injective.
  miappend :: MIdeal r -> r -> MIdeal r

instance MonoidIdeal Ordering where
  type MIdeal Ordering = Bool
  misplit EQ = Nothing
  misplit LT = Just False
  misplit GT = Just True
  miembed False = LT
  miembed True  = GT
  x `miappend` _ = x

instance MonoidIdeal () where
  type MIdeal () = Void
  misplit () = Nothing
  miembed _ = ()
  x `miappend` _ = x

instance MonoidIdeal Any where
  type MIdeal Any = ()
  misplit (Any True)  = Just ()
  misplit (Any False) = Nothing
  miembed () = Any True
  () `miappend` _ = ()

instance MonoidIdeal All where
  type MIdeal All = ()
  misplit (All False) = Just ()
  misplit (All True)  = Nothing
  miembed () = All False
  () `miappend` _ = ()

instance MonoidIdeal [a] where
  type MIdeal [a] = NonEmpty a
  misplit []     = Nothing
  misplit (x:xs) = Just (x :| xs)
  miembed (x :| xs) = x:xs
  (x :| xs) `miappend` ys = x :| (xs ++ ys)

instance (Monoid r) => MonoidIdeal (Maybe r) where
  type MIdeal (Maybe r) = r
  misplit x = x
  mifuse x = x
  r `miappend` Nothing = r
  r `miappend` (Just a) = r `mappend` a

instance MonoidIdeal (First r) where
  type MIdeal (First r) = r
  misplit (First x) = x
  miembed x = First $ Just x
  r `miappend` _ = r

instance MonoidIdeal (Last r) where
  type MIdeal (Last r) = r
  misplit (Last x) = x
  miembed x = Last $ Just x
  r `miappend` Last Nothing  = r
  _ `miappend` Last (Just x) = x

instance MonoidIdeal (Sum Word) where
  type MIdeal (Sum Word) = Word
  misplit (Sum 0) = Nothing
  misplit (Sum x) = Just x
  miembed 0 = error ""
  miembed x = Sum x
  0 `miappend` _     = error ""
  x `miappend` Sum y = x + y

-- | Ideal of the product of two ideal monoids.
data MaybeProduct a b = MLeft a | MRight b | MBoth a b

instance (MonoidIdeal a, MonoidIdeal b) => MonoidIdeal (a, b) where
  type MIdeal (a, b) = MaybeProduct (MIdeal a) (MIdeal b)
  misplit (a, b) = case (misplit a, misplit b) of
                     (Nothing, Nothing) -> Nothing
                     (Just a,  Nothing) -> Just $ MLeft  a
                     (Nothing, Just b)  -> Just $ MRight b
                     (Just a,  Just b)  -> Just $ MBoth  a b
  miembed (MLeft  a)   = (miembed a, mempty)
  miembed (MRight b)   = (mempty, miembed b)
  miembed (MBoth  a b) = (miembed a, miembed b)
  m `miappend` (x, y) =
    fromJust $ misplit (a `mappend` x, b `mappend` y)
      where
       (a, b) = miembed m

-- | Check if a value of an ideal monoid is the unit.
isUnit :: (MonoidIdeal m) => m -> Bool
isUnit = maybe True (const False) . misplit
