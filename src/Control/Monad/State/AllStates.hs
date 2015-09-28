{-# LANGUAGE MultiParamTypeClasses,
             FlexibleInstances,
             FlexibleContexts,
             DeriveFunctor,
             GeneralizedNewtypeDeriving
 #-}

{-|
Module      : Control.Monad.State.AllStates
Copyright   : (c) 2015 Maciej Piróg
License     : MIT
Maintainer  : maciej.adam.pirog@gmail.com
Stability   : experimental

A monad transformer that is similar to the state monad, but it
accumulates all intermediate states in a (possibly infinite!)
stream.

The @'AllStatesT'@ transformer is similar to
@'Control.Monad.State.SnapStates.SnapStatesT'@,
but it snaps every new state. The conversion functions between
@'AllStatesT'@ and @'Control.Monad.State.SnapStates.SnapStatesT'@
are defined in the module "Control.Monad.State.SnapStates".
-}
module Control.Monad.State.AllStates
  (
    -- * The @AllStatesT@ monad transformer

    AllStatesT(..),
    allToState,
    stateToAll,

    -- * The @AllStates@ monad

    AllStates,
    execAllStates

    -- * Examples

    -- ** Tree Traversal

    -- $treeTraversal

    -- ** While language
    
    -- $whileLang

    -- * Implementation

    -- $impl
  )
  where

import Control.Applicative (Applicative, WrappedMonad(..))
import Control.Monad (liftM)
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Identity (Identity(..))
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.Writer (WriterT(..))
import Control.Monad.State (MonadState(..), StateT(..))
import Control.Monad.Free (Free(..), liftF)
import Data.Functor.Apply (Apply)
import Data.Functor.Bind (Bind)

import Control.Monad.Module.Resumption (Resumption(..), liftMonad)

-- | A monad transformer that acts like @'StateT'@, but it also
-- records every intermediate state in a stream. If the stream is
-- finite, it is terminated with the final value of type @a@.
--
-- Technically, the @'AllStatesT'@ transformer is the resumption
-- monad generated by the fact that @'WriterT' s r@ (understood as
-- a functor, not a monad!) is a right module over @'ReaderT' s m@
-- if @r@ is a right module over @m@. This means that, modulo
-- @newtype@ constructors, it is equal to:
--
-- @
-- F m s x = m (x, s)
-- AllStatesT s m a = s -> m ('Free' (F m s) a)
-- @
--
-- Note that the stream (that is, the @'Free'@ part of the
-- datatype) could be empty
-- (e.g.
-- @'AllStatesT' $ 'Resumption' $ 'ReaderT' $ \\s -> 'return' 2@),
-- which means that the computation does not produce a new state.
-- Such a value is a pure computation.
newtype AllStatesT s m a = AllStatesT { runAllStatesT ::
  Resumption (ReaderT s m) (WriterT s (WrappedMonad m)) a }
 deriving(Functor, Applicative, Monad, Apply, Bind)

instance MonadTrans (AllStatesT s) where
  lift = AllStatesT . liftMonad . lift 

instance (Monad m) => MonadState s (AllStatesT s m) where
  get = AllStatesT $ Resumption $ ReaderT $
    \s -> return $ Pure s
  put s = AllStatesT $ Resumption $ ReaderT $
    \_ -> return $ liftF $ WriterT $ return ((), s)

-- | Forget the intermediate states. It is a monad morphism.
allToState :: (Monad m) => AllStatesT s m a -> StateT s m a
allToState (AllStatesT (Resumption (ReaderT r))) =
  StateT $ \s -> r s >>= aux s
 where
  aux s (Pure a)                       = return (a, s)
  aux _ (Free (WriterT (WrapMonad m))) = m >>= \(f, s) -> aux s f

-- | Lift @'StateT'@ to @'AllStatesT'@. It is NOT a monad morphism.
stateToAll :: (Monad m) => StateT s m a -> AllStatesT s m a
stateToAll (StateT f) = AllStatesT $ Resumption $ ReaderT $
  \s -> liftM (\(a,s) -> Free $ WriterT $ return (Pure a, s)) (f s)

-- | A monad that acts like @'State'@, but it also records every
-- intermediate state in a (possibly infinite!) stream. If the
-- stream is finite, it is terminated with the final value.
type AllStates s = AllStatesT s Identity

-- | Evaluate a @'AllStates'@ computation and extract the list of
-- all intermediate states. If the computation is non-terminating,
-- the list is infinite.
execAllStates :: AllStates s a -> s -> [s]
execAllStates (AllStatesT (Resumption (ReaderT t))) s =
  fromFree $ runIdentity $ t s
 where
  fromFree (Pure _)                                       = []
  fromFree (Free (WriterT (WrapMonad (Identity (f, s))))) =
    s : fromFree f

{- $treeTraversal

We statefully traverse a binary tree, looking for the greatest
value in the leaves. The datatype of trees and the traversing
function are as follows:

@
data Tree a = Leaf a | Node (Tree a) (Tree a)

searchMax :: (Ord a, MonadState a m) => Tree a -> m ()
searchMax (Leaf a)   = do max <- get
                          if a > max then put a else return ()
searchMax (Node a b) = do searchMax a
                          searchMax b
@

Consider the following tree:

@
tree :: Tree Int
tree = Node
  (Node (Node (Leaf 2) (Leaf 3)) (Node (Leaf 1) (Leaf 7)))
  (Node (Node (Leaf 4) (Leaf 5)) (Node (Leaf 9) (Leaf 6)))
@

It corresponds to:

@
         _______|_______
        |               |
     ___|___         ___|___
    |       |       |       |
   _|_     _|_     _|_     _|_
  |   |   |   |   |   |   |   |
  2   3   1   7   4   5   9   6
@

We execute @searchMax@ using the @'AllStates'@ monad and extract
the intermediate states:

>>> execAllStates (searchMax tree) 0
[2,3,7,9]

The result is the list of all the states that were the \"current\"
maximal element at some point of the computation.
-}

{- $whileLang
Another example is an interpreter of the While language. The syntax
is given by the following abstract syntax:

@
-- Type of variable identifiers
type VarId = String
\ 
-- Arithmetic expressions
data Arith = Var VarId                           -- Variable
           | C Int                               -- Constant
           | Op (Int -> Int -> Int) Arith Arith  -- Operator
\ 
-- Language statements
data Cmd = Cmd :>>: Cmd      -- Composition of programs (semicolon)
         | VarId := Arith    -- Assignment
         | If Arith Cmd Cmd  -- If statement
         | While Arith Cmd   -- While statement
\ 
infixl 2 :>>:
infixl 3 :=
@

We can interpret arithmetic expressions and program statements in
any @'MonadState'@. We assume
\"@import qualified Data.Map as Map@\".

@
type Memory = Map.Map VarId Int

interpA :: (MonadState Memory m) => Arith -> m Int
interpA (Var x)    = liftM (fromJust . Map.lookup x) get
interpA (C n)      = return n
interpA (Op f a b) = liftM2 f (interpA a) (interpA b)

interp :: (MonadState Memory m) => Cmd -> m ()
interp (c :>>: d)  = interp c >> interp d
interp (x := t)    = liftM2 (Map.insert x) (interpA t) get >>= put
interp (If b c d)  = do x <- interpA b
                        interp $ if x /= 0 then c else d
interp (While b c) = do x <- interpA b
                        when (x /= 0) $ interp c >> interp (While b c)
@

Let's run a program. For example, the factorial of 4:

@
fact :: Cmd
fact =
 \"x\" := C 4 :>>:
 \"total\" := C 1 :>>:
 While (Op (\\a b -> if a >= b then 1 else 0) (Var \"x\") (C 1))
 (
   \"total\" := Op (*) (Var \"total\") (Var \"x\") :>>:
   \"x\" := Op (-) (Var \"x\") (C 1)
 )
@

We interpret it in an empty memory:

>>> execAllStates (interp fact) Map.empty
[fromList [("x",4)],
 fromList [("total",1),("x",4)],
 fromList [("total",4),("x",4)],
 fromList [("total",4),("x",3)],
 fromList [("total",12),("x",3)],
 fromList [("total",12),("x",2)],
 fromList [("total",24),("x",2)],
 fromList [("total",24),("x",1)],
 fromList [("total",24),("x",1)],
 fromList [("total",24),("x",0)]
]

Each element of the resulting list is a snapshot of the memory
taken at each assignment.

@
diverge :: Cmd
diverge =
 \"x\" := C 1 :>>:
 While (C 1)
 (
   \"x\" := Op (*) (Var \"x\") (C 2)
 )
@

The program diverges, so there is no final state. But, if we
interpret it using the @'AllStates'@ monad, we obtain an infinite
list of the intermediate states:

>>> execAllStates (interp diverge) Map.empty
[fromList [("x",1)],
 fromList [("x",2)],
 fromList [("x",4)],
 fromList [("x",8)],
 fromList [("x",16)],
 fromList [("x",32)],
 fromList [("x",64)],
 fromList [("x",128)],...

-}


{- $impl

The @'AllStatesT'@ transformer is simply the @'Resumption'@
monad generated by the module @'WriterT' s m@ (understood as a
functor: we ignore the monadic part of @'WriterT'@, that is,
we do not need @s@ to be an instance of @'Data.Monoid.Monoid'@)
over the monad transformer @'ReaderT' s m@.
However, it is useful to understand what this monad looks like
in this instance.

First, we look at the underlying monad, @'AllStates'@. A value of
@'AllStates' s a@ is of the following shape (ignoring @newtype@
 constructors):

@
\\s -> Free (Free (Free (Pure a, s3), s2), s1)
@

This is a computation that takes an initial state @s@, and then
it accumulates the states @s1@, @s2@, and @s3@. The return value
is @a@.

A non-terminating computation looks like the following:

@
\\s -> let f n = Free (f (n + 1), n) in f s
@

Note that the free part of the monad does not have a bottom, so
there is no final value @a@.

A pure computation @'return' a@ is given as:

@
\\s -> Pure a
@

It does not produce a new state. The return value of the @'State'@
monad, which could be encoded in the @'AllStates'@ monad as
@\\s -> 'Free' ('Pure' a, s)@, produces a new state, which prolongs
the stream by one element. This is why @'stateToAll'@ is not a
monad morphism.

We illustrate the @'join'@ operation with the following:

@
  join $ \\s -> Free (Free (Free (Pure f, s3), s2), s1)
=
  \\s -> Free (Free (Free (f s3, s3), s2), s1)
@

For example, we can illustrate the right unit law with:

@
  join $ \\s -> Free (Free (Free (Pure (return \"hi\"), s3), s2), s1)
=
  join $ \\s -> Free (Free (Free (Pure (\\t -> Pure \"hi\"), s3), s2), s1)
=
  \\s -> Free (Free (Free ((\\t -> Pure \"hi\") s3, s3), s2), s1)
=
  \\s -> Free (Free (Free (Pure \"hi\", s3), s2), s1)
@

If the inner expression doesn't have any @'Free'@ layers,
the @'join'@ of @'Reader'@ is performed:

@
  join $ \\s -> Pure f
=
  \\s -> f s
= (eta reduction)
  f
@

-}
