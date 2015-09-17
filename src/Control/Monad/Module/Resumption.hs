{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, RankNTypes, DeriveFunctor, GeneralizedNewtypeDeriving #-}

{-|
Module      : Resumption
Description : Generalised resumption monad
Copyright   : (c) 2015 Maciej Piróg
License     : MIT
Maintainer  : maciej.adam.pirog@gmail.com
Stability   : experimental

Generalised resumption monad a la M. Piróg, N. Wu, J. Gibbons
/Modules over monads and their algebras/
<https://coalg.org/calco15/papers/p18-Piróg.pdf>.
-}
module Control.Monad.Module.Resumption
  (
    -- * Datatype of generalised resumptions
    Resumption(..),
    MNonPure(..),
    liftm,
    liftr,
    foldResumption,
    interpResumption,
    unfold,
    -- * Moggi's monad transformers
    -- $moggiR
    FM,
    MoggiResumption(..),
    force,
    hold,
    foldFM,
    foldMoggiR,
    interpFM,
    interpMoggiR,
    RRRResumption(..),
    runRRRR
  )
  where

import Control.Applicative (Applicative(..), WrappedMonad(..))
import Control.Monad (ap, liftM)
import Control.Monad.Free (Free(..), iter, foldFree, liftF)
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Identity (Identity(..))
import Data.Functor.Compose (Compose(..))

import Control.Monad.Module
import Control.Monad.Free.NonPure hiding (unfoldNonPure)

-- | The generalised resumption monad is a composition of a monad
-- @m@ and the free monad generated by @r@ (intended to be a right
-- module over @m@).
newtype Resumption m r a =
  Resumption { unResumption :: m (Free r a) }
 deriving (Functor)

ext :: (RModule m r) => (a -> Resumption m r b) -> Free r a -> m (Free r b)
ext f (Pure a) = unResumption $ f a
ext f (Free r) = return $ Free $ r |>>= ext f

instance (RModule m r) => Monad (Resumption m r) where
  return = Resumption . return . return
  Resumption m >>= f = Resumption $ m >>= ext f

instance (Functor m, RModule m r) => Applicative (Resumption m r) where
  pure = return
  (<*>) = ap

-- | Type of resumptions with at least one level of free structure.
newtype MNonPure m r a = MNonPure { unMNonPure :: m (NonPure r a) }
 deriving (Functor)

instance (Functor m, RModule m r) => RModule (Resumption m r) (MNonPure m r) where
   MNonPure m |>>= f = MNonPure $
     fmap (\(NonPure r) -> NonPure $ r |>>= ext f) m

instance (Functor m, RModule m r) => Idealised (Resumption m r) (MNonPure m r) where
  embed (MNonPure m) = Resumption $ fmap (Free . unNonPure) m

-- | Lifts a computation in a monad @m@ to a computation in the
-- resumption monad.
liftm :: (RModule m r) => m a -> Resumption m r a
liftm = Resumption . liftM Pure

-- | Lifts a value of a right module over a monad @m@ to a
-- computation in the resumption monad.
liftr :: (RModule m r) => r a -> Resumption m r a
liftr = Resumption . return . Free . fmap Pure

-- | Fold the structure of a resumption using an @m@-algebra and
-- and @r@-algebra.
foldResumption :: (Functor m, Functor r) => (m a -> a) -> (r a -> a) -> Resumption m r a -> a
foldResumption f g (Resumption m) = f $ fmap (iter g) m

-- | Fold the structure of a resumption by interpreting each layer
-- as a computation in a monad @k@ and then @'join'@-ing the
-- layers.
interpResumption :: (Functor k, Monad k) => (forall a. m a -> k a) -> (forall a. r a -> k a) -> Resumption m r a -> k a
interpResumption f g (Resumption m) = f m >>= foldFree g

-- | Unfold structure step-by-step.
unfold :: (Functor m, RModule m r) => (s -> Either a (m (r s))) -> s -> Resumption m r a
unfold f s = case f s of
               Left  a -> return a
               Right m -> (Resumption $ fmap liftF m) >>= unfold f

--
-- Moggi's monad transformers
--

-- $moggiR
-- In a paper /An Abstract View of Programming Languages/
-- E. Moggi presented a monad that in Haskell could be implemented
-- as follows (assume @m@ to be a monad, and @f@ to be a functor):
--
-- @newtype Res f m a = Res (m ('Either' a (f (Res f m a))))@
--
-- It could be shown that Moggi's monad corresponds to the
-- @'Resumption'@ monad for a module given by:
--
-- @'Compose' f ('WrappedMonad' m)@
--
-- Moggi's monad is sometimes called the /free monad transformer/
-- and is used, for example, in the @pipes@ package.

-- | A composition of a functor @f@ and a monad @m@. It is a module
-- over @m@.
--
-- In fact, it is the free module in the category of modules over
-- @m@ generated by @f@. So @'FM'@ can stand for \"composition
-- of @f@ and @m@\", or \"free module\".
type FM f m = Compose f (WrappedMonad m)

-- | A wrapper for resumptions a la Moggi.
newtype MoggiResumption f m a =
  MoggiR { unMoggiR :: Resumption m (FM f m) a}
 deriving (Functor, Monad, Applicative)

instance (Functor f) => MonadTrans (MoggiResumption f) where
  lift = MoggiR . liftm

-- | Get one level of computation out of a resumption. Inverse of @'hold'@.
force :: (Functor f, Monad m) => MoggiResumption f m a -> m (Either a (f (MoggiResumption f m a)))
force (MoggiR (Resumption m)) = liftM aux m
 where
  aux (Pure a) = Left a 
  aux (Free (Compose f)) =
    Right $ fmap (MoggiR . Resumption . unwrapMonad) f
 
-- | Hold a computation and store it in a resumption. Inverse of @'force'@.
hold :: (Functor f, Monad m) => m (Either a (f (MoggiResumption f m a))) -> MoggiResumption f m a
hold m = MoggiR $ Resumption $ liftM aux m
 where
  aux (Left a)  = Pure a
  aux (Right f) = Free $ Compose $ fmap (WrapMonad . unResumption . unMoggiR) f

foldFM :: (Functor f) => (f a -> a) -> (m a -> a) -> FM f m a -> a
foldFM g h (Compose f) = g $ fmap (h . unwrapMonad) f

-- | Fold the structure of a Moggi resumption using an @f@-algebra and an @m@-algebra.
foldMoggiR :: (Functor m, Monad m, Functor f) => (f a -> a) -> (m a -> a) -> MoggiResumption f m a -> a
foldMoggiR g h = foldResumption h (foldFM g h) . unMoggiR

interpFM :: (Monad k) => (forall a. f a -> k a) -> (forall a. m a -> k a) -> Compose f (WrappedMonad m) a -> k a 
interpFM g h (Compose f) = g f >>= (h . unwrapMonad)

-- | Fold the structure of a resumption by interpreting each layer
-- as a computation in a monad @k@ and then @'join'@-ing the
-- layers.
interpMoggiR :: (Functor k, Monad k) => (forall a. f a -> k a) -> (forall a. m a -> k a) -> MoggiResumption f m a -> k a
interpMoggiR g h = interpResumption h (interpFM g h) . unMoggiR

-- | A wrapper for resumptions based on the right-regular
-- representation module.
type RRRResumption = MoggiResumption Identity

-- | Run a resumption as a single computation
runRRRR :: (Functor m, Monad m) => RRRResumption m a -> m a
runRRRR = interpMoggiR (return . runIdentity) id
