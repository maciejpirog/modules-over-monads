{-# LANGUAGE TypeFamilies,
             FlexibleInstances,
             FlexibleContexts,
             MultiParamTypeClasses,
             TypeOperators,
             TupleSections
 #-}

{-|
Module      : Control.Monad.Module
Copyright   : (c) 2015 Maciej Piróg
License     : MIT
Maintainer  : maciej.adam.pirog@gmail.com
Stability   : experimental

Haskell implementation of

* Left and right modules over monads. 
For abstract nonsense, consult M. Piróg, N. Wu, J. Gibbons
/Modules over monads and their algebras/
<https://coalg.org/calco15/papers/p18-Piróg.pdf>.

* Idealised and ideal monads.
For abstract nonsense, consult S. Milius
/Completely iterative algebras and completely iterative monads/
<http://www.iti.cs.tu-bs.de/~milius/phd/M1.pdf>.
-}
module Control.Monad.Module
  (
    -- * Right modules over monads

    RModule(..),
    RId,
    wrapId,

    -- ** Example: State and \"Writer\"

    -- $stateAndWriter

    -- * Left modules over monads

    LModule(..),

    -- * Idealised monads

    Idealised(..),

    -- * Ideal monads

    MonadIdeal(..),
    fuse,
    restriction,
    extension
  )
  where

import Control.Monad (liftM)
import Control.Applicative (Const(..), WrappedMonad(..))
import Control.Monad.Identity (Identity(..))
import Control.Monad.Free (Free(..))
import Control.Monad.State (StateT(..), State(..), runState)
import Control.Monad.Reader (Reader, runReader, ReaderT(..))
import Control.Monad.Writer (Writer, runWriter, WriterT(..))
import Control.Monad.Codensity (Codensity(..))
import Control.Comonad.Env (EnvT(..), Env(..))
import Data.Void (Void(..))
import Data.Functor.Compose (Compose(..))
import Data.List.NonEmpty (NonEmpty(..))

import Control.Monad.Free.NonPure (NonPure(..))
import Data.List.AtLeast2 (AtLeast2(..), fromNonEmpty, toNonEmpty)
import Data.Monoid.MonoidIdeal (MonoidIdeal(..))

--
-- RIGHT MODULES
--

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

-- | Each monad can be seen as its own module with @'|>>='@ given
-- by @'>>='@. To distinguish between the uses of a monad as a
-- monad and as its module, we do not define the following
-- instance:
--
-- @instance Monad m => RModule m m@
--
-- Instead, we wrap the use of @m@ as a module in @'WrappedMonad'@:
--
-- @instance Monad m => RModule m (WrappedMonad m)@
--
-- Since we sometimes use datatypes of monad transformers as
-- \"module transformers\", the type @'WrappedMonad' 'Identity'@
-- occurs pretty often. For example, it is the case that
--
-- @instance (RModule m r) => RModule (ReaderT s m) (WriterT s r)@
--
-- but it does not mean that
--
-- @instance RModule (Reader s) (Writer s)@
--
-- Rather, it is the case that
--
-- @instance RModule (Reader s) (WriterT s (WrappedMonad Identity))@
--
-- This could be alternatively written as:
--
-- @instance RModule (Reader s) (WriterT s RId)@
type RId = WrappedMonad Identity

-- | Wrap a value in both @'Identity'@ and @'WrapMonad'@.
wrapId :: a -> RId a
wrapId = WrapMonad . Identity

{- $stateAndWriter

In this example, for clarity (?), we ignore @newtype@ constructors.
The @'Control.Monad.State.State'@ monad can be defined as follows:

@
type State s a = s -> (a, s)
return a = \\s -> (a, s)
f >>= g = \\s -> let (a, s') = f s in g a s'
@

We use the @'Control.Monad.Writer.Writer'@ datatype, but we do not
use its monadic structure. So, for our purposes, it is defined as:

@
type Writer s a = (a, s)
@

The Writer datatype is the execution context, as it provides the
initial state, and records the final value and the final state:

@
actr :: Writer s (State s a) -> Writer s a
   -- = (State s a, s) -> (a, s)
actr (f, s) = f s 
@
-}

--
-- LEFT MODULES
--

{- | Left modules are /op/-dual to right modules. Instances should
satisfy the following:

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

--
-- IDEALISED MONADS
--

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

--
-- IDEAL MONADS
--

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

* @'either' 'return' 'embed' . 'split'  =  'id'@

* @'split' . 'either' 'return' 'embed'  =  'id'@
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

-- | Restrict an ideal monad morphism (= monad morphism that
-- preserves @'split'@) to the ideal.
restriction :: (MonadIdeal m, MonadIdeal n) => (m a -> n a) -> (Ideal m a -> Ideal n a)
restriction f = aux . split . f . embed
 where
  aux (Right i) = i
  aux (Left _)  = error "not an ideal monad morphism"

-- | Extend a morphism of ideals (a natural transformation that
-- commutes with @'|>>='@) to the whole monad.
extension :: (MonadIdeal m, MonadIdeal n) => (Ideal m a -> Ideal n a) -> m a -> n a
extension f m = case split m of
                  Left a  -> return a
                  Right i -> embed $ f i
--
-- R-INSTANCES
--

-- | Right regular representation
instance (Monad m) => RModule m (WrappedMonad m) where
  WrapMonad m |>>= k = WrapMonad (m >>= k)

instance (Monad m) => Idealised m (WrappedMonad m) where
  embed = unwrapMonad

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

-- NonEmpty + AtLeast2

instance RModule NonEmpty AtLeast2 where
  m |>>= f = fromNonEmpty $ toNonEmpty m >>= f

instance Idealised NonEmpty AtLeast2 where
  embed = toNonEmpty

instance MonadIdeal NonEmpty where
  type Ideal NonEmpty = AtLeast2
  split (x :| []) = Left x
  split xs        = Right $ fromNonEmpty xs

-- ReaderT + WriterT

instance (RModule m r) => RModule (ReaderT s m) (WriterT s r) where
  WriterT r |>>= f =
    WriterT $ r |>>= \(a, s) -> liftM (, s) $ runReaderT (f a) s

-- ReaderR + EnvT

instance (RModule m r) => RModule (ReaderT s m) (EnvT s r) where
  EnvT s r |>>= f =
    EnvT s $ r |>>= \a -> runReaderT (f a) s

-- StateT + WriterT

instance (RModule m r) => RModule (StateT s m) (WriterT s r) where
  WriterT r |>>= f =
    WriterT $ r |>>= \(a, s) -> runStateT (f a) s

-- State + Env (NOT StateT + EnvT !!!)

instance RModule (State s) (Env s) where
  EnvT s (Identity a) |>>= f =
    let Identity (a', s') = runStateT (f a) s
     in EnvT s' (Identity a')

-- MonoidIdeal

instance (MonoidIdeal w, i ~ MIdeal w, RModule m r) => RModule (WriterT w m) (WriterT i r) where
  WriterT r |>>= f = WriterT $ r |>>=
    \(a, i) -> liftM (\(b, w) -> (b, i `mir` w)) $ runWriterT $ f a

instance (MonoidIdeal w, i ~ MIdeal w, Idealised m r) => Idealised (WriterT w m) (WriterT i r) where
  embed (WriterT r) = WriterT $ embed $
                        fmap (\(a, w) -> (a, miembed w)) r

instance (MonoidIdeal r) => MonadIdeal (Writer r) where
  type Ideal (Writer r) = WriterT (MIdeal r) (WrappedMonad Identity)
  split w  = case misplit r of
               Nothing -> Left a
               Just i  -> Right $ WriterT $ WrapMonad $ Identity (a, i)
   where
    (a, r) = runWriter w

-- Free

instance (Functor f) => RModule (Free f) (NonPure f) where
  (NonPure f) |>>= g = NonPure (fmap (>>= g) f)

instance (Functor f) => Idealised (Free f) (NonPure f) where
  embed = Free . unNonPure

instance (Functor f) => MonadIdeal (Free f) where
  type Ideal (Free f) = NonPure f
  split (Pure x) = Left x
  split (Free f) = Right $ NonPure f

--
-- L-INSTANCES
--

-- | Left regular representation
instance (Monad m) => LModule m (WrappedMonad m) where
  m >>=| k = WrapMonad (m >>= unwrapMonad . k)

instance (Functor f) => LModule (Codensity f) f where
  Codensity g >>=| h = g h
