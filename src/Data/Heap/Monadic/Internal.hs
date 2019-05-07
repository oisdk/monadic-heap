{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_HADDOCK not-home #-}
------------------------------------------------------------------------
-- |
-- Module      : Data.Heap.Monadic.Internal
-- Copyright   : Donnacha Oisín Kidney 2019
-- License     : Apache 2.0
-- Portability : GHC

module Data.Heap.Monadic.Internal where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Star
import           Control.Monad.Writer
import           Data.Function
import           Data.Group
import qualified Data.Heap.Pairing.Internal as Heap
import           Data.List                  (unfoldr)
import           GHC.Base                   (build)
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
    mconcat = fromListWith id
    {-# INLINE mconcat #-}

instance (Group a, Ord a) => Applicative (Heap a) where
    pure x = Tree (Node mempty x Nil)
    Empty <*> _ = Empty
    Tree _ <*> Empty = Empty
    Tree fs <*> Tree xs = Tree (fs <*> xs)

instance (Group a, Ord a) => Applicative (Node a) where
    pure x = Node mempty x Nil
    Node fw f fs <*> xs = fw <>! mergeNs1 (<*> xs) (fmap f xs) fs

instance (Group a, Ord a) => Monad (Node a) where
    Node k x xs >>= f = k <>! mergeNs1 (>>= f) (f x) xs

instance (Group a, Ord a) => Monad (Heap a) where
    Empty    >>= _ = Empty
    Tree xs' >>= f = goN xs'
      where
        goN (Node w x xs) = w <>* (mergeHs goN xs <> f x)

instance (Group a, Ord a) => Alternative (Heap a) where
    empty = mempty
    (<|>) = (<>)
    {-# INLINE empty #-}
    {-# INLINE (<|>) #-}

instance (Group a, Ord a) => MonadPlus (Heap a)

-- |
-- 'prio' @x@ @y@ constructs a singleton heap with a value @y@ and a
-- priority @x@.
prio :: a -> b -> Heap a b
prio x y = Tree (Node x y Nil)
{-# INLINE prio #-}

-- | Get the item with the lowest key.
popMin :: (Ord a, Group a) => Heap a b -> Maybe ((a,b), Heap a b)
popMin Empty                = Nothing
popMin (Tree (Node x y xs)) = Just ((x,y), x <>* mergeQs xs)
{-# INLINE popMin #-}

-- | Get all items, in ascending order of keys.
prios :: (Ord a, Group a) => Heap a b -> [(a,b)]
prios = unfoldr popMin
{-# INLINE prios #-}

mergeHs :: (Ord a, Group a) => (Node a b -> Heap a c) -> Forest a b -> Heap a c
mergeHs _ Nil       = Empty
mergeHs f (x :- xs) = mergeHs1 f (f x) xs
{-# INLINE mergeHs #-}

mergeHs1 :: (Ord a, Group a) => (Node a b -> Heap a c) -> Heap a c -> Forest a b -> Heap a c
mergeHs1 f = go
  where
    go x Nil               = x
    go x1 (x2 :- Nil)      = x1 <> f x2
    go x1 (x2 :- x3 :- xs) = (x1 <> f x2) <> go (f x3) xs
{-# INLINE mergeHs1 #-}

mergeNs :: (Ord a, Group a) => (Node a b -> Node a c) -> Forest a b -> Heap a c
mergeNs _ Nil       = Empty
mergeNs f (x :- xs) = Tree (mergeNs1 f (f x) xs)
{-# INLINE mergeNs #-}

mergeNs1 :: (Ord a, Group a) => (Node a b -> Node a c) -> Node a c -> Forest a b -> Node a c
mergeNs1 f = go
  where
    go x Nil               = x
    go x1 (x2 :- Nil)      = x1 <> f x2
    go x1 (x2 :- x3 :- xs) = (x1 <> f x2) <> go (f x3) xs
{-# INLINE mergeNs1 #-}

mergeQs :: (Ord a, Group a) => Forest a b -> Heap a b
mergeQs = mergeNs id
{-# INLINE mergeQs #-}

-- | Returns the entries, grouped by values with the same weights.
samePrios :: (Ord a, Group a, Ord b) => Heap a b -> [(a, [b])]
samePrios xs' = build (go xs')
  where
    go Empty _ n                = n
    go (Tree (Node w x xs)) c n = go' w (x Heap.:< Heap.Nil) (mergeQs xs) c n

    go' w xs Empty c n = c (w, Heap.toList xs) n
    go' w xs (Tree (Node yw y ys)) c n
      | yw == mempty = go' w (Heap.insert y xs) (mergeQs ys) c n
      | otherwise    = (w, Heap.toList xs) `c` go' yw (y Heap.:< Heap.Nil) (mergeQs ys) c n
{-# INLINE samePrios #-}

-- | Returns a list of values, ordered first by their priorities and then
-- by the values themselves.
-- This order is what is used to define the law-abiding instances,
-- although it is less efficient to produce than prios.
ordPrios :: (Ord a, Group a, Ord b) => Heap a b -> [(a, b)]
ordPrios xs = samePrios xs >>= sequenceA
{-# INLINE ordPrios #-}

-- | Construct a heap from a list of keys with priorities.
fromList :: (Ord a, Group a) => [(a,b)] -> Heap a b
fromList = fromListWith (uncurry prio)

fromListWith :: (Ord a, Group a) => (c -> Heap a b) -> [c] -> Heap a b
fromListWith _ []       = Empty
fromListWith f (x : xs) = fromListWith1 f (f x) xs
{-# INLINE fromListWith #-}

fromListWith1 :: (Ord a, Group a) => (c -> Heap a b) -> Heap a b -> [c] -> Heap a b
fromListWith1 f = go
  where
    go x []              = x
    go x1 [x2]           = x1 <> f x2
    go x1 (x2 : x3 : xs) = (x1 <> f x2) <> go (f x3) xs
{-# INLINE fromListWith1 #-}

nFromListWith :: (Ord a, Group a) => (c -> Node a b) -> Node a b -> [c] -> Node a b
nFromListWith f = go
  where
    go x []              = x
    go x1 [x2]           = x1 <> f x2
    go x1 (x2 : x3 : xs) = (x1 <> f x2) <> go (f x3) xs
{-# INLINE nFromListWith #-}

foldrComm :: (a -> b -> b) -> b -> Heap k a -> b
foldrComm f = flip go
  where
    go Empty b     = b
    go (Tree xs) b = goN xs b
    goN (Node _ x xs) b = f x (goF xs b)
    goF Nil b       = b
    goF (x :- xs) b = goN x (goF xs b)
{-# INLINE foldrComm #-}

foldlComm' :: (b -> a -> b) -> b -> Heap k a -> b
foldlComm' _ !b Empty = b
foldlComm' f !b' (Tree xs') = goN b' xs'
  where
    goN !b (Node _ x xs) = goF (f b x) xs
    goF !b Nil       = b
    goF !b (x :- xs) = goF (goN b x) xs
{-# INLINE foldlComm' #-}

foldMapW' :: (Semigroup w, Monoid b) => (a -> w -> b) -> Heap w a -> b
foldMapW' _ Empty     = mempty
foldMapW' f (Tree xs) = foldMapWN' f xs
{-# INLINE foldMapW' #-}

foldMapWN' :: (Semigroup w, Semigroup b) => (a -> w -> b) -> Node w a -> b
foldMapWN' f (Node w' x' xs') = goF w' (f x' w') xs'
  where
    goN !i (Node w x xs) = goF iw (f x iw) xs
      where
        !iw = i <> w
    goF !_ !x Nil               = x
    goF !i !x1 (x2 :- Nil)      = x1 <> goN i x2
    goF !i !x1 (x2 :- x3 :- xs) = (x1 <> goN i x2) <> goF i (goN i x3) xs
{-# INLINE foldMapWN' #-}

instance (Ord a, Group a) => Foldable (Heap a) where
    foldr f = flip go
      where
        go Empty b                = b
        go (Tree (Node _ x xs)) b = f x (go (mergeQs xs) b)
    {-# INLINE foldr #-}
    length = foldlComm' (\a _ -> a + 1) 0
    sum = foldlComm' (+) 0
    product = foldlComm' (*) 1
    null Empty = True
    null _     = False
    elem x = foldrComm (\y b -> x == y || b) False

instance (Ord a, Group a, Ord b) => Eq (Heap a b) where
    (==) = (==) `on` samePrios

instance (Ord a, Group a, Ord b) => Ord (Heap a b) where
    compare = compare `on` samePrios

instance (Ord a, Group a, Show a, Show b) => Show (Heap a b) where
    showsPrec n xs s = "fromList " ++ showsPrec n (prios xs) s

instance (Ord a, Group a) => Traversable (Heap a) where
    traverse f = fmap fromList . (traverse.traverse) f . prios

instance (Ord a, Group a) =>
         MonadWriter a (Node a) where
    writer (x,w) = Node w x Nil
    tell w = Node w () Nil
    listen (Node w x xs) = Node w (x, w) (go w xs)
      where
        go _ Nil = Nil
        go i (Node k y zs :- ys) = Node k (y, ik) (go ik zs) :- go i ys
          where
            ik = i <> k
    pass = foldMapWN' (\(x , f) w -> Node (f w) x Nil)

instance (Ord a, Group a) =>
         MonadWriter a (Heap a) where
    writer = uncurry (flip prio)
    tell = flip prio ()
    listen Empty     = Empty
    listen (Tree xs) = Tree (listen xs)
    pass Empty     = Empty
    pass (Tree xs) = Tree (pass xs)

instance (Group a, Ord a)
      => MonadStar (Heap a) where
    star f x' = Tree (Node mempty x' (go (f x')))
      where
        go Empty = Nil
        go (Tree (Node k x xs)) =
          Node k x (go (mergeNs id xs <> f x)) :- Nil
