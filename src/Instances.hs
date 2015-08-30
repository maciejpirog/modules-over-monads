{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances, DeriveFunctor, GeneralizedNewtypeDeriving, TypeOperators #-}

module Instances
  (
    -- * Non-empty list
    AtLeast2(..),
    -- * Free monad
    Wrap(..)
  )
  where

import Control.Applicative (Const(..), WrappedMonad(..))
import Control.Monad.Identity (Identity(..))
import Control.Monad.Free (Free(..))
import Control.Monad.State (State(..), runState)
import Control.Monad.Reader (Reader, runReader, ReaderT(..))
import Control.Monad.Writer (Writer, runWriter, WriterT(..))
import Data.Void (Void(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Functor.Compose (Compose(..))

import Module

-- Regular representations

-- | Right regular representation
instance (Functor m, Monad m) => RModule m (WrappedMonad m) where
  WrapMonad m |>>= k = WrapMonad (m >>= k)

-- | Left regular representation
instance (Functor m, Monad m) => LModule m (WrappedMonad m) where
  m >>=| k = WrapMonad (m >>= unwrapMonad . k)

-- Composition

instance (Functor f, RModule m r) => RModule m (f `Compose` r) where
  Compose f |>>= k = Compose $ fmap (|>>= k) f

-- Identity

instance RModule Identity (Const Void) where
  Const x |>>= _ = Const x

instance Idealised Identity (Const Void) where
  embed _ = error "constant void..."

instance AdjoinedUnit Identity where
  type Ideal Identity = Const Void
  split (Identity a)  = Left a

instance MonadIdeal Identity

-- Maybe

instance RModule Maybe (Const ()) where
  Const _ |>>= _ = Const ()

instance Idealised Maybe (Const ()) where
  embed _ = Nothing

instance AdjoinedUnit Maybe where
  type Ideal Maybe = Const ()
  split (Just a)  = Left a
  split (Nothing) = Right $ Const ()

instance MonadIdeal Maybe

-- Either

instance RModule (Either e) (Const e) where
  Const x |>>= _ = Const x

instance Idealised (Either e) (Const e) where
  embed (Const e) = Left e

instance AdjoinedUnit (Either e) where
  type Ideal (Either e) = Const e
  split (Left  e) = Right $ Const e
  split (Right a) = Left  a

instance MonadIdeal (Either e)

-- NonEmpty

{- | List with at least two elements -}
data AtLeast2 a = a :|: NonEmpty a
  deriving (Functor)

infixr 4 :|:

fromNonEmpty :: NonEmpty a -> AtLeast2 a
fromNonEmpty (x :| y : xs) = x :|: y :| xs

toNonEmpty :: AtLeast2 a -> NonEmpty a
toNonEmpty (x :|: y :| xs) = x :| y : xs

instance RModule NonEmpty AtLeast2 where
  m |>>= f = fromNonEmpty $ toNonEmpty m >>= f

instance Idealised NonEmpty AtLeast2 where
  embed = toNonEmpty

instance AdjoinedUnit NonEmpty where
  type Ideal NonEmpty = AtLeast2
  split (x :| []) = Left x
  split xs        = Right $ fromNonEmpty xs

instance MonadIdeal NonEmpty

-- Free

{- | Free monad generated by a functor @f@ wrapped in @f@. In other
words, it is the type of \"free monads\" with at least one layer of
@f@.
-}
newtype Wrap f a = Wrap { unWrap :: f (Free f a) }
 deriving (Functor)

instance (Functor f) => RModule (Free f) (Wrap f) where
  (Wrap f) |>>= g = Wrap (fmap (>>= g) f)

instance (Functor f) => Idealised (Free f) (Wrap f) where
  embed = Free . unWrap

instance (Functor f) => AdjoinedUnit (Free f) where
  type Ideal (Free f) = Wrap f
  split (Pure x) = Left x
  split (Free f) = Right $ Wrap f

instance (Functor f) => MonadIdeal (Free f)

-- Reader + Writer

instance RModule (Reader s) (Writer s) where
  w |>>= f = WriterT $ Identity $ (runReader (f a) s, s)
   where (a, s)  = runWriter w

-- State + Writer

instance RModule (State s) (Writer s) where
  w |>>= f = WriterT $ Identity $ runState (f a) s
   where (a, s)  = runWriter w

{-

module Instances
  (
    Const(..),
    MonoidIdeal(..),
    Void(..),
    NotEmpty(..),
  )
  where

import Ideal
import Data.Word
import Data.Monoid
import Data.Functor.Identity
import Control.Monad.Trans.Error
import Control.Monad.Writer

data Const x y = Const x
  deriving (Functor)

-- Maybe

instance MonadIdeal Maybe where
  type Ideal Maybe = Const ()
  split (Just a)  = Left a
  split (Nothing) = Right $ Const ()
  embed (Const _) = Nothing
  Const _ |>>= _ = Const ()

-- Either

instance MonadIdeal (Either e) where
  type Ideal (Either e) = Const e
  split (Left  e) = Right $ Const e
  split (Right a) = Left  a
  embed (Const e) = Left e
  Const x |>>= _ = Const x

-- Writer

{- | A 'Writer' monad is ideal if an only if the underlying monoid
is a semigroup with freely adjoined unit, which is captured by the 
'MonoidIdeal' class.
-}
class (Monoid r) => MonoidIdeal r where

  -- | Type of elements of the semigroup.
  type MIdeal r :: *

  -- | Check if the argument is the adjoined unit (return value
  -- @Nothing@) or an element of the semigroup @r@ (return value
  -- @Just x@).
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
  -- but this would lead to ambiguity, as 'MIdeal' is not necessarily
  -- injective.
  miappend :: MIdeal r -> r -> MIdeal r

instance MonoidIdeal Ordering where
  type MIdeal Ordering = Bool
  misplit EQ = Nothing
  misplit LT = Just False
  misplit GT = Just True
  miembed False = LT
  miembed True  = GT
  x `miappend` _ = x

data Void

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

data NotEmpty a = a :| [a]
  deriving (Functor)

instance MonoidIdeal [a] where
  type MIdeal [a] = NotEmpty a
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

instance (MonoidIdeal r) => MonadIdeal (Writer r) where
  type Ideal (Writer r) = Writer (MIdeal r)
  split w  = case misplit r of
               Nothing -> Left a
               Just i  -> Right $ WriterT $ Identity (a, i)
   where
    (a, r) = runWriter w
  embed (WriterT (Identity (a, w))) =
     WriterT $ Identity (a, miembed w) 
  WriterT (Identity (a, w)) |>>= f =
     case f a of
       WriterT (Identity (b, r)) ->
         WriterT $ Identity (b, w `miappend` r)

-}