{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, TypeOperators #-}

{-|
Module      : Module
Description : Left and right modules over monads, idealised and
              ideal monads
Copyright   : (c) 2015 Maciej Piróg
License     : MIT
Maintainer  : maciej.adam.pirog@gmail.com
Stability   : experimental

Haskell implementation of

* Left and right modules over monads. 
For abstract nonsense, consult M. Piróg, N. Wu, J. Gibbons /Modules over monads and their algebras/ <https://coalg.org/calco15/papers/p18-Piróg.pdf>.

* Idealised and ideal monads.
For abstract nonsense, consult S. Milius /Completely iterative algebras and completely iterative monads/ <http://www.iti.cs.tu-bs.de/~milius/phd/M1.pdf>.
-}
module Control.Monad.Module
  (
    -- * Right modules over monads
    RModule(..),
    -- * Left modules over monads
    LModule(..),
    -- * Idealised and ideal monads
    Idealised(..),
    MonadIdeal(..),
    fuse
  )
  where

import Control.Monad (liftM)
import Control.Applicative (Const(..), WrappedMonad(..))
import Control.Monad.Identity (Identity(..))
import Control.Monad.Free (Free(..))
import Control.Monad.State (State(..), runState)
import Control.Monad.Reader (Reader, runReader, ReaderT(..))
import Control.Monad.Writer (Writer, runWriter, WriterT(..))
import Control.Monad.Codensity (Codensity(..))
import Data.Void (Void(..))
import Data.Functor.Compose (Compose(..))


import Data.Monoid.MonoidIdeal (MonoidIdeal(..))

{- | Captures the relationship of a functor being a /right module/
over a monad, which is a similar concept to modules over rings or
modules over groups (aka /G/-sets) in abstract algebra. Modules can
be seen as structures that consume monadic computations.

Instances should satisfy the following laws:

* @t '|>>=' 'return'  =  t@

* @(t '|>>=' f) '|>>=' g  =  t '|>>=' (f '>=>' g)@
-}
class (Functor r, Monad m) => RModule m r where

  -- | Bind any computation in the monad to a value of the module.
  (|>>=) :: r a -> (a -> m b) -> r b
  r |>>= h = actr $ fmap h r

  -- | Join a computation with the outer level given by the module.
  actr :: r (m a) -> r a
  actr r = r |>>= id

{- | Left modules are /op/-dual to right modules. Instances should satisfy the following:

* @'return' a '>>=|' f  =  f a@

* @(m '>>=' f) '>>=|' g  =  m '>>=|' (\\x -> f x '>>=|' g)@
-}
class (Functor l, Monad m) => LModule m l where

  -- | Bind a value of the module to a monadic computation.
  (>>=|) :: m a -> (a -> l b) -> l b
  m >>=| h = actl $ liftM h m

  -- | Join a computation with the outer level given by the module.
  actl :: m (l a) -> l a
  actl m = m >>=| id

{- | Captures the fact that the monad @m@ is /idealised/ with @r@.
This means that @r@ represents a subset of computations in @m@
closed under binding with any other computation. Intuitively, @r@
contains computations with an invariant that cannot be lost by
binding more actions. For example, if we write a non-empty string
to a @'Writer' 'String'@, we cannot obtain a writer with an empty
buffer by means of monadic composition.

Instances should satisfy the following law:

* @'embed' t '>>=' f  =  'embed' (t '|>>=' f)@
-}
class (RModule m r) => Idealised m r where

  -- | Represent a computation in @r@ as a computation in @m@.
  embed :: r a -> m a

{- | The 'MonadIdeal' class is a subclass of 'Monad' with the
following property: Given an ideal monad @m@, each value of @m a@
is either a pure value of the type @a@ (this can be obtained with
the 'return' function), or an abstract action. Moreover, a pure
value cannot be obtained by binding a non-pure action with any
other value (intuitively: once we perform an action, we cannot undo
it). More formally, a datatype @m a@ is (isomorphic to) a disjoint
sum of @a@ and @f a@ for some functor @f@, which is called an
/ideal/ of @m@. In category-theoretic terms, an ideal monad is a
semigroupad with freely adjoined unit.

Instances should satisfy the following:

* @'either' 'return' 'embed' . 'split' = 'id'@

* @'split' . 'either' 'return' 'embed' = 'id'@
-}
class (Idealised m (Ideal m)) => MonadIdeal m where

  -- | Type of non-pure computations, that is, others than those
  -- obtained with @'return'@.
  type Ideal m :: * -> *

  -- | Represent a monad as a disjoint sum of pure values and
  -- non-pure computations.
  split :: m a -> Either a (Ideal m a)

-- | Reconstruct a monad from either a return value or an ideal.
-- A right and left inverse of @'split'@.
fuse :: (MonadIdeal m) => Either a (Ideal m a) -> m a
fuse (Left  a) = return a
fuse (Right r) = embed r

--
-- R-INSTANCES
--

-- | Right regular representation
instance (Monad m) => RModule m (WrappedMonad m) where
  WrapMonad m |>>= k = WrapMonad (m >>= k)

-- Composition

instance (Functor f, RModule m r) => RModule m (f `Compose` r) where
  Compose f |>>= k = Compose $ fmap (|>>= k) f

-- Identity

instance RModule Identity (Const Void) where
  Const x |>>= _ = Const x

instance Idealised Identity (Const Void) where
  embed _ = error "constant void..."

instance MonadIdeal Identity where
  type Ideal Identity = Const Void
  split (Identity a)  = Left a

-- Maybe

instance RModule Maybe (Const ()) where
  Const _ |>>= _ = Const ()

instance Idealised Maybe (Const ()) where
  embed _ = Nothing

instance MonadIdeal Maybe where
  type Ideal Maybe = Const ()
  split (Just a)  = Left a
  split (Nothing) = Right $ Const ()

-- Either

instance RModule (Either e) (Const e) where
  Const x |>>= _ = Const x

instance Idealised (Either e) (Const e) where
  embed (Const e) = Left e

instance MonadIdeal (Either e) where
  type Ideal (Either e) = Const e
  split (Left  e) = Right $ Const e
  split (Right a) = Left  a

-- Reader + Writer

instance RModule (Reader s) (Writer s) where
  w |>>= f = WriterT $ Identity $ (runReader (f a) s, s)
   where (a, s)  = runWriter w

-- State + Writer

instance RModule (State s) (Writer s) where
  w |>>= f = WriterT $ Identity $ runState (f a) s
   where (a, s)  = runWriter w

-- MonoidIdeal

instance (MonoidIdeal r, i ~ MIdeal r) => RModule (Writer r) (Writer i) where
  WriterT (Identity (a, w)) |>>= f =
     case f a of
       WriterT (Identity (b, r)) ->
         WriterT $ Identity (b, w `mir` r)

instance (MonoidIdeal r, i ~ MIdeal r) => Idealised (Writer r) (Writer i) where
  embed (WriterT (Identity (a, w))) =
     WriterT $ Identity (a, miembed w) 

instance (MonoidIdeal r) => MonadIdeal (Writer r) where
  type Ideal (Writer r) = Writer (MIdeal r)
  split w  = case misplit r of
               Nothing -> Left a
               Just i  -> Right $ WriterT $ Identity (a, i)
   where
    (a, r) = runWriter w

--
-- L-INSTANCES
--

-- | Left regular representation
instance (Monad m) => LModule m (WrappedMonad m) where
  m >>=| k = WrapMonad (m >>= unwrapMonad . k)

instance (Functor f) => LModule (Codensity f) f where
  Codensity g >>=| h = g h
