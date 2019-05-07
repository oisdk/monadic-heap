module Data.Heap.Pairing.Internal where

import GHC.Base

infixr 5 :-
infixr 5 :<
data Heap a = Empty | Tree {-# UNPACK #-} !(Node a)
data Node a = !a :< Forest a
data Forest a = Nil | (:-) {-# UNPACK #-} !(Node a) (Forest a)

mergeNodes :: Ord a => Node a -> Node a -> Node a
mergeNodes xh@(x :< xs) yh@(y :< ys)
  | x <= y    = x :< yh :- xs
  | otherwise = y :< xh :- ys
{-# INLINE mergeNodes #-}

mergeQs :: Ord a => Node a -> Forest a -> Node a
mergeQs x Nil = x
mergeQs x1 (x2 :- Nil) = mergeNodes x1 x2
mergeQs x1 (x2 :- x3 :- xs) = mergeNodes (mergeNodes x1 x2) (mergeQs x3 xs)

insert :: Ord a => a -> Node a -> Node a
insert x yh@(y :< ys)
  | x <= y    = x :< yh :- Nil
  | otherwise = y :< (x :< Nil) :- ys
{-# INLINE insert #-}

popMin :: Ord a => Heap a -> Maybe (a, Heap a)
popMin Empty = Nothing
popMin (Tree (x :< xs)) = Just (x, case xs of Nil -> Empty; y :- ys -> Tree (mergeQs y ys) )
{-# INLINE popMin #-}

toList :: Ord a => Node a -> [a]
toList xs' = build (go xs')
  where
    go (x :< xs) c n = c x (go' xs c n)

    go' Nil _ n = n
    go' (x :- xs) c n = go (mergeQs x xs) c n
{-# INLINE toList #-}
