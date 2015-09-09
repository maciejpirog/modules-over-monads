{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances, DeriveFunctor #-}

{-|
Module      : Resumption
Description : Ideal monoids (semigroups with freely adjoined unit)
Copyright   : (c) 2015 Maciej Piróg
License     : MIT
Maintainer  : maciej.adam.pirog@gmail.com
Stability   : experimental

A monoid is /ideal/ if it has a trivial unit. In detail, a monoid
is ideal if it has the following two features:

* It is decidable if a value of the monoid is its unit (that is,
  the value obtained with @'mempty'@). An example of such a monoid
  is given by lists with the monoid multiplication (@'mappend'@)
  given by concatenation (@'++'@): it is easy to check if a list is
  empty. A non-example is the monoid of functions @a -> a@ with
  the monoid multiplication given by composition. In general, it is
  undecidable if a given function is equal to the identity.

* The monoid is /positive/ (aka /zerosumfree/, /conical/, or
  /centerless/). This means that for all @a@ and @b@ such that
  @'mappend' a b = 'mempty'@,
  it is the case that @a = b = 'mempty'@. In other words, there is 
  no way to obtain the unit by multiplying non-unit elements
  (e.g. you cannot obtain @0@ by adding together positive, nonzero
  integers). Note that the non-unit (that is, other than
  @'mempty'@) elements of a positive monoid form a semigroup; even
  more: an /ideal/ of the monoid.

/Said in the language of abstract nonsense:/
An ideal monoid is obtained by freely adjoining a unit to a
semigroup. That is, it is an image of a semigroup via the left
adjoint to the forgetful functor from the category of monoids to
the category of semigroups.

/A note on implementation:/
One way to implement ideal monoids is to explicitly state the
\"abstract nonsense\" approach and say that an ideal monoid is a
disjoint sum of a semigroup and a \"unit\", that is, it is the
familiar monoid instance:

@ ('Semigroup' s) => 'Monoid' ('Maybe' s) @

However, we want to treat /being/ an ideal monoid as a property of
a monoid, not necessarily construct it explicitly as a @'Maybe s'@ from a semigroup @'s'@. That is, we want a @'Monoid'@ subcalss,
which we call @'MonoidIdeal'@. Each instance @'MonoidIdeal' m@
contains a type of the ideal (@'MIdeal' m@), and functions
(necessarily isomorphisms) that allow @m@ to be seen as a disjoint
sum of @'MIdeal' m@ and the adjoined unit.
-}

module Data.Monoid.MonoidIdeal
  (
    -- * @'MonoidIdeal'@ typeclass
    MonoidIdeal(..),
    -- * Products of ideal monoids
    -- $prods
    IdealProduct(..),
    -- * Additional functions
    isUnit
  )
  where

import Data.Monoid
import Data.Word
import Data.Void
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromJust)

{- | The class of ideal monoids. Instances should satisfy:

@ misplit . mifuse = 'id' @

@ mifuse . misplit = 'id' @

@ misplit . 'mzero' = 'Nothing' @

@ miembed = mifuse . 'Just' @

@ miappend x ('mappend' a b) = miappend (miappend x a) b @

@ miappend x 'mzero' = x @

-}
class (Monoid r) => MonoidIdeal r where

  -- | Type of elements of the ideal of the non-unit elements of
  -- the monoid @r@.
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
  r `miappend` Nothing  = r
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

-- $prods
-- Monoids have products, that is, if @a@ and @b@ are monoids,
-- then @(a,b)@ is a monoid with pointwise multiplication.
-- A product of two ideal monoids is also ideal, with the assocated
-- ideal given by the set of those pairs @(x,y)@ such that
--
-- * @x@ is an element of @a@, and @y@ is an element of @b@,
--
-- * it is not the case that both @x@ and @y@ are units of the
--   respective monoids.

-- | Ideal of the product of two ideal monoids.
data IdealProduct a b = MLeft (MIdeal a)
                      | MRight (MIdeal b)
                      | MBoth (MIdeal a) (MIdeal b)
-- deriving (Functor)
-- the above doesn't work with GHC 7.4.1

instance (MonoidIdeal a, MonoidIdeal b) => MonoidIdeal (a, b) where
  type MIdeal (a, b) = IdealProduct a b
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