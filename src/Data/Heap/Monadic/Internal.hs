{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns  #-}

{-# OPTIONS_HADDOCK not-home #-}
------------------------------------------------------------------------
-- |
-- Module      : Data.Heap.Monadic.Internal
-- Copyright   : Donnacha Oisín Kidney 2019
-- License     : Apache 2.0
-- Portability : GHC

module Data.Heap.Monadic.Internal where

import Data.Group
import Control.Applicative
import Control.Monad
import Data.List (unfoldr)

-- | A pairing heap with priorities in a.
data Heap a b
    = Empty
    | Tree {-# UNPACK #-} !(Node a b)
    deriving Functor

data Node a b
    = Node !a b (Forest a b)
    deriving Functor

infixr 5 :-
data Forest a b
    = Nil
    | (:-) {-# UNPACK #-} !(Node a b) (Forest a b)
    deriving Functor

(<>!) :: Semigroup a => a -> Node a b -> Node a b
x <>! Node y z ys = Node (x <> y) z ys
{-# INLINE (<>!) #-}

(<>*) :: Semigroup a => a -> Heap a b -> Heap a b
_ <>* Empty = Empty
x <>* Tree xs = Tree (x <>! xs)
{-# INLINE (<>*) #-}

instance (Ord a, Group a) => Semigroup (Node a b) where
  Node x xv xs <> Node y yv ys
    | x <= y    = Node x xv (Node (inv x <> y) yv ys :- xs)
    | otherwise = Node y yv (Node (inv y <> x) xv xs :- ys)
  {-# INLINE (<>) #-}

instance (Ord a, Group a) => Semigroup (Heap a b) where
    Empty <> ys = ys
    xs <> Empty = xs
    Tree xs <> Tree ys = Tree (xs <> ys)
    {-# INLINE (<>) #-}

instance (Ord a, Group a) => Monoid (Heap a b) where
    mempty = Empty
    mappend = (<>)
    {-# INLINE mempty #-}
    {-# INLINE mappend #-}

instance (Group a, Ord a) => Applicative (Heap a) where
    pure x = Tree (Node mempty x Nil)
    Empty <*> _ = Empty
    Tree _ <*> Empty = Empty
    Tree fs <*> Tree xs = Tree (goN mempty fs)
      where
        goN i (Node k v Nil) = (i <> k) <>! fmap v xs
        goN i (Node k v (g :- gs)) = (ik <>! fmap v xs) <> goF ik g gs
          where ik = i <> k

        goF i g1 Nil = goN i g1
        goF i g1 (g2 :- Nil) = goN i g1 <> goN i g2
        goF i g1 (g2 :- g3 :- gs) = (goN i g1 <> goN i g2) <> goF i g3 gs

instance (Group a, Ord a) => Monad (Heap a) where
  xs' >>= f = goH mempty xs'
    where
      goN i (Node k v xs) = (ik <>* f v) <> goF ik xs
        where ik = i <> k

      goH _ Empty = Empty
      goH i (Tree xs) = goN i xs

      goF _ Nil = Empty
      goF i (x :- xs) = goF' i x xs

      goF' i x1 Nil = goN i x1
      goF' i x1 (x2 :- Nil) = goN i x1 <> goN i x2
      goF' i x1 (x2 :- x3 :- xs) = (goN i x1 <> goN i x2) <> goF' i x3 xs

instance (Group a, Ord a) => Alternative (Heap a) where
    empty = mempty
    (<|>) = (<>)

instance (Group a, Ord a) => MonadPlus (Heap a)

-- |
-- 'prio' @x@ @y@ constructs a singleton heap with a value @y@ and a
-- priority @x@.
prio :: a -> b -> Heap a b
prio x y = Tree (Node x y Nil)
{-# INLINE prio #-}

mergeQs :: (Ord a, Group a) => Forest a b -> Heap a b
mergeQs Nil = Empty
mergeQs (x :- xs) = Tree (go x xs)
  where
    go t Nil = t
    go t1 (t2 :- Nil) = t1 <> t2
    go t1 (t2 :- t3 :- ts) = (t1 <> t2) <> go t3 ts

-- | Get the item with the lowest key.
popMin :: (Ord a, Group a) => Heap a b -> Maybe ((a,b), Heap a b)
popMin Empty = Nothing
popMin (Tree (Node x y xs)) = Just ((x,y), x <>* mergeQs xs)
{-# INLINE popMin #-}

-- | Get all items, in ascending order of keys.
prios :: (Ord a, Group a) => Heap a b -> [(a,b)]
prios = unfoldr popMin
{-# INLINE prios #-}

-- | Construct a heap from a list of keys with priorities.
fromList :: (Ord a, Group a) => [(a,b)] -> Heap a b
fromList = foldMap (uncurry prio)

foldrComm :: (a -> b -> b) -> b -> Heap k a -> b
foldrComm f = flip go
  where
    go Empty b = b
    go (Tree xs) b = goN xs b
    goN (Node _ x xs) b = f x (goF xs b)
    goF Nil b = b
    goF (x :- xs) b = goN x (goF xs b)

foldlComm' :: (b -> a -> b) -> b -> Heap k a -> b
foldlComm' _ !b Empty = b
foldlComm' f !b' (Tree xs') = goN b' xs'
  where
    goN !b (Node _ x xs) = goF (f b x) xs
    goF !b Nil = b
    goF !b (x :- xs) = goF (goN b x) xs
{-# INLINE foldlComm' #-}

instance (Ord a, Group a) => Foldable (Heap a) where
    foldr f = flip go
      where
        go Empty b = b
        go (Tree (Node _ x xs)) b = f x (go (mergeQs xs) b)
    {-# INLINE foldr #-}
    length = foldlComm' (\a _ -> a + 1) 0
    sum = foldlComm' (+) 0
    product = foldlComm' (*) 1
    null Empty = True
    null _ = False
    elem x = foldrComm (\y b -> x == y || b) False

instance (Ord a, Group a, Eq b) => Eq (Heap a b) where
    xs == ys = prios xs == prios ys

instance (Ord a, Group a, Ord b) => Ord (Heap a b) where
    compare xs ys = compare (prios xs) (prios ys)

instance (Ord a, Group a, Show a, Show b) => Show (Heap a b) where
    showsPrec n xs s = "fromList " ++ showsPrec n (prios xs) s

instance (Ord a, Group a) => Traversable (Heap a) where
    traverse f = fmap fromList . (traverse.traverse) f . prios
