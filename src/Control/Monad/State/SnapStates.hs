{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, DeriveFunctor, GeneralizedNewtypeDeriving #-}

module Control.Monad.State.SnapStates
  (
    -- * The @'SnapStatesT'@ transformer

    SnapStatesT(..),
    SnapStates,
    snap,
    stateToSnap,
    snapToState,
    execSnapStates
  )
  where

import Control.Applicative (Applicative, WrappedMonad(..))
import Control.Monad (liftM)
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Identity (Identity(..))
import Control.Monad.Writer (WriterT(..))
import Control.Monad.State (MonadState(..), StateT(..))
import Control.Monad.Free (Free(..), liftF)
import Data.Functor.Apply (Apply)
import Data.Functor.Bind (Bind)

import Control.Monad.Module.Resumption (Resumption(..), liftm)

-- | A monad transformer that acts like @'StateT'@, but it also
-- records selected intermediate states in a (possibly infinite!)
-- stream. To save the current state, use the @'snap'@ function.
-- If the stream is finite, it is terminated with the final value.
--
-- The @'SnapStatesT'@ transformer is the resumption monad
-- generated by the fact that @'WriterT s r'@ (understood as a
-- functor, not a monad!) is a right module over @'ReaderT s m'@
-- if @r@ is a right module over @m@. Modulo @newtype@
-- constructors, it is equal to:
--
-- @
-- F m s x = m (x, s)
-- AllStatesT s m a = s -> m ('Free' (F m s) a, s)
-- @
newtype SnapStatesT s m a = SnapStatesT { runAllStatesT ::
  Resumption (StateT s m) (WriterT s (WrappedMonad m)) a }
 deriving(Functor, Applicative, Monad, Apply, Bind)

type SnapStates s = SnapStatesT s Identity

instance MonadTrans (SnapStatesT s) where
  lift = SnapStatesT . liftm . lift 

instance (Monad m) => MonadState s (SnapStatesT s m) where
  get = stateToSnap get
  put = stateToSnap . put

-- | Save the current state to the stream.
snap :: (Monad m) => SnapStatesT s m ()
snap = SnapStatesT $ Resumption $ StateT $ \s -> return (Free $ WriterT $ return (Pure (), s), s)

-- | Lift @'StateT'@ to @'AllStatesT'@. It is a monad morphism.
stateToSnap :: (Monad m) => StateT s m a -> SnapStatesT s m a
stateToSnap = SnapStatesT . liftm

-- | Forget the intermediate states. It is a monad morphism.
snapToState :: (Monad m) => SnapStatesT s m a -> StateT s m a
snapToState (SnapStatesT (Resumption (StateT f))) =
  StateT $ \s -> f s >>= \(g, s') -> aux s' g
 where
  aux s (Pure a) = return (a, s)
  aux s (Free (WriterT (WrapMonad m))) = m >>= \(f, s') -> aux s' f

-- | Evaluate a @'SnapStates'@ computation and extract the list of
-- the snapped states (+ the final state). If the computation is
-- non-terminating, the list is infinite.
execSnapStates :: SnapStates s a -> s -> [s]
execSnapStates (SnapStatesT (Resumption (StateT t))) s =
  s' : fromFree f
 where
  Identity (f, s') = t s
  fromFree (Pure _)                                       = []
  fromFree (Free (WriterT (WrapMonad (Identity (f, s))))) =
    s : fromFree f