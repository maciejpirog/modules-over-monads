{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, DeriveFunctor, GeneralizedNewtypeDeriving #-}

module Resumption
  (
    Resumption(..),
    MWrap(..),
    liftm,
    liftr
  )
  where

import Control.Applicative (Applicative(..))
import Control.Monad (ap)
import Control.Monad.Free

import Module
import Instances

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

newtype MWrap m r a = MWrap { unMWrap :: m (Wrap r a) }
 deriving (Functor)

instance (Functor m, RModule m r) => RModule (Resumption m r) (MWrap m r) where
   MWrap m |>>= f = MWrap $
     fmap (\(Wrap r) -> Wrap $ r |>>= ext f) m

instance (Functor m, RModule m r) => Idealised (Resumption m r) (MWrap m r) where
  embed (MWrap m) = Resumption $ fmap (Free . unWrap) m

liftm :: (Functor m, RModule m r) => m a -> Resumption m r a
liftm = Resumption . fmap return

liftr :: (Functor m, RModule m r) => r a -> Resumption m r a
liftr = Resumption . return . Free . fmap Pure
