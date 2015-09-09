{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, RankNTypes #-}

{-|
Module      : IdealCoproduct
Description : Coproduct of ideal monads
Copyright   : (c) 2015 Maciej Piróg
License     : MIT
Maintainer  : maciej.adam.pirog@gmail.com
Stability   : experimental

Haskell implementation of the coproduct of two ideal monads. For
abstract nonsense, consult N. Ghani, T. Uustalu
/Coproducts of ideal monads/
<http://www.cs.ioc.ee/~tarmo/papers/fics03-tia.pdf>.
-}
module Control.Monad.Module.IdealCoproduct
  (
    Turns(..),
    IdealCoproduct(..),
    sym,
    AmbiTurns(..),
    liftl,
    liftr,
    foldTurns,
    foldIdealCoproduct,
    interpTurns,
    interpIdealCoproduct
  )
  where

import Control.Applicative(Applicative(..))
import Control.Monad(ap)

import Control.Monad.Module

-- | Values of @Turns h t a@ can be seen as interleaved layers of
-- the functors @h@ and @t@ (they /take turns/) with variables of
-- the type @a@ possible on every level (except for the outermost
-- layer, which is always given by @h@).
newtype Turns h t a =
  Turns { unTurns :: h (Either a (Turns t h a)) }

instance (Functor t, Functor h) => Functor (Turns t h) where
  fmap f (Turns t) = Turns $ fmap aux t
   where
    aux (Left  x) = Left  $ f x
    aux (Right y) = Right $ fmap f y

-- | The coproduct (a disjoint sum in the category of ideal monads)
-- of ideal monads @m@ and @n@. Each value consists of alternating
-- layers of the ideals of @m@ and @n@ with variables of the type
-- @a@.
data IdealCoproduct m n a =
    ICVar a
  | ICLeft  (Turns (Ideal m) (Ideal n) a)
  | ICRight (Turns (Ideal n) (Ideal m) a)

-- | Swap the 'ICLeft' and 'ICRight' constructors. The function 'sym' is an involution, that is, @sym . sym = id@.
sym :: IdealCoproduct m n a -> IdealCoproduct n m a
sym (ICVar   a) = ICVar   a
sym (ICLeft  a) = ICRight a
sym (ICRight a) = ICLeft  a

toM :: (MonadIdeal m, MonadIdeal n) => IdealCoproduct m n a -> m (Either a (Turns (Ideal n) (Ideal m) a))
toM (ICVar   a) = return $ Left a
toM (ICLeft  i) = embed  $ unTurns i
toM (ICRight i) = return $ Right i

(|>>-) :: (MonadIdeal m, MonadIdeal n) => Turns (Ideal m) (Ideal n) a -> (a -> IdealCoproduct m n b) -> Turns (Ideal m) (Ideal n) b
Turns x |>>- f = Turns $ x |>>= aux
 where
  aux (Left  a) = toM (f a)
  aux (Right i) = return $ Right $ i |>>- (sym . f)

instance (Functor (Ideal m), Functor (Ideal n)) => Functor (IdealCoproduct m n) where
  fmap f (ICVar   a) = ICVar   $ f a
  fmap f (ICLeft  i) = ICLeft  $ fmap f i
  fmap f (ICRight i) = ICRight $ fmap f i

instance (MonadIdeal m, MonadIdeal n) => Monad (IdealCoproduct m n) where
  return = ICVar
  ICVar   a >>= f = f a
  ICLeft  i >>= f = ICLeft  $ i |>>- f
  ICRight i >>= f = ICRight $ i |>>- (sym . f)

instance (MonadIdeal m, MonadIdeal n) => Applicative (IdealCoproduct m n) where
  pure = return
  (<*>) = ap

-- | The ideal of 'IdealCoproduct'.
newtype AmbiTurns h t a = AmbiTurns 
  { unAmbiTurns :: (Either (Turns h t a) (Turns t h a)) }

instance (Functor h, Functor t) => Functor (AmbiTurns h t) where
  fmap f (AmbiTurns (Left  i)) = AmbiTurns $ Left  $ fmap f i
  fmap f (AmbiTurns (Right i)) = AmbiTurns $ Right $ fmap f i

instance (MonadIdeal m, MonadIdeal n) => MonadIdeal (IdealCoproduct m n) where
  type Ideal (IdealCoproduct m n) = AmbiTurns (Ideal m) (Ideal n)
  split (ICVar   a) = Left a
  split (ICLeft  i) = Right $ AmbiTurns $ Left  i
  split (ICRight i) = Right $ AmbiTurns $ Right i

instance (MonadIdeal m, MonadIdeal n, i ~ AmbiTurns (Ideal m) (Ideal n)) => RModule (IdealCoproduct m n) i where
  AmbiTurns (Left  i) |>>= f = AmbiTurns $ Left  $ i |>>- f
  AmbiTurns (Right i) |>>= f = AmbiTurns $ Right $ i |>>- (sym . f)

instance (MonadIdeal m, MonadIdeal n, i ~ AmbiTurns (Ideal m) (Ideal n)) => Idealised (IdealCoproduct m n) i where
  embed (AmbiTurns (Left  i)) = ICLeft  i
  embed (AmbiTurns (Right i)) = ICRight i  

-- | Lift an ideal monad @m@ to @IdealCoproduct m n@. The function
-- 'inl' respects the equations of the 'MonadTrans' class, that is:
--
-- * @'liftl' . 'return'  =  'return'@
--
-- * @'liftl' m '>>=' 'liftl' . f  =  'liftl' (m '>>=' f)@
liftl :: (MonadIdeal m, MonadIdeal n) => m a -> IdealCoproduct m n a
liftl m = case split m of
            Left  a  -> ICVar a
            Right m' -> ICLeft $ Turns $ fmap Left m'

-- | Symmetric version of 'liftl'.
liftr :: (MonadIdeal m, MonadIdeal n) => n a -> IdealCoproduct m n a
liftr = sym . liftl

-- | Fold the structure of a 'Turns' using an @h@-algebra and a
-- @t@-algebra.
foldTurns :: (Functor h, Functor t) => (h a -> a) -> (t a -> a) -> Turns h t a -> a
foldTurns f g (Turns t) = f $ fmap aux t
 where
  aux (Left  a) = a
  aux (Right i) = foldTurns g f i

-- | Fold the structure of an 'IdealCoproduct' using an @m@-algebra
-- and a @n@-algebra.
foldIdealCoproduct :: (MonadIdeal m, MonadIdeal n) => (m a -> a) -> (n a -> a) -> IdealCoproduct m n a -> a
foldIdealCoproduct f g (ICVar   a) = a
foldIdealCoproduct f g (ICLeft  i) =
  foldTurns (f . embed) (g . embed) i
foldIdealCoproduct f g (ICRight i) =
  foldTurns (g . embed) (f . embed) i

-- | Fold the structure of a 'Turns' by interpreting each level as
-- a computation in a monad @k@ and then @'join'@-ing them to
-- obtain one computation in @k@.
interpTurns :: (Monad k) => (forall a. h a -> k a) -> (forall a. t a -> k a) -> Turns h t a -> k a
interpTurns f g (Turns h) = f h >>= aux
 where
  aux (Left  a) = return a
  aux (Right i) = interpTurns g f i

-- | Fold the structure of an 'IdealCoproduct' by interpreting each
-- level as a computation in a monad @k@ and then @'join'@-ing them
-- to obtain one computation in @k@.
-- From the category-theoretic point of view, if the first two
-- arguments are ideal monad morphisms, @'interpIdealCoproduct'@ is
-- the coproduct mediator.
interpIdealCoproduct :: (MonadIdeal m, MonadIdeal n, Monad k) => (forall a. m a -> k a) -> (forall a. n a -> k a) -> IdealCoproduct m n a -> k a
interpIdealCoproduct f g (ICVar   a) = return a
interpIdealCoproduct f g (ICLeft  i) =
  interpTurns (f . embed) (g . embed) i
interpIdealCoproduct f g (ICRight i) =
  interpTurns (g . embed) (f . embed) i
