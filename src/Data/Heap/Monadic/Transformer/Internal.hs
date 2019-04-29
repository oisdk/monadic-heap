{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE LambdaCase            #-}

{-# OPTIONS_HADDOCK not-home #-}

module Data.Heap.Monadic.Transformer.Internal where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Reader.Class
import           Control.Monad.State.Class
import           Control.Monad.Error.Class
import           Control.Monad.Trans.Class
import           Data.Group

newtype HeapT a m b = HeapT
    { runHeapT :: m (Tree a m b)
    } deriving Functor

data Tree a m b
  = Empty
  | Tree !(Node a m b)
  deriving Functor

data Node a m b
  = Node !a b (Forest a m b)
  deriving Functor

newtype NodeT a m b = NodeT
    { runNodeT :: m (Node a m b)
    } deriving (Functor)

infixr 5 :-
data Forest a m b
  = Nil
  | (:-) (NodeT a m b) (Forest a m b)
  deriving Functor

(<>!) :: Semigroup a => a -> Node a m b -> Node a m b
x <>! Node y z ys = Node (x <> y) z ys
{-# INLINE (<>!) #-}

(<>*) :: Semigroup a => a -> Tree a m b -> Tree a m b
_ <>* Empty = Empty
x <>* Tree xs = Tree (x <>! xs)
{-# INLINE (<>*) #-}

instance (Ord a, Group a, Applicative m) => Semigroup (Node a m b) where
  Node x xv xs <> Node y yv ys
    | x <= y    = Node x xv (NodeT (pure (Node (inv x <> y) yv ys)) :- xs)
    | otherwise = Node y yv (NodeT (pure (Node (inv y <> x) xv xs)) :- ys)
  {-# INLINE (<>) #-}

instance (Ord a, Group a, Applicative m) => Semigroup (Tree a m b) where
    Empty <> ys = ys
    xs <> Empty = xs
    Tree xs <> Tree ys = Tree (xs <> ys)
    {-# INLINE (<>) #-}

instance (Group a, Ord a, Monad m) => Applicative (HeapT a m) where
    pure x = HeapT (pure (Tree (Node mempty x Nil)))
    (<*>) = ap

instance (Group a, Ord a, Monad m) => Monad (HeapT a m) where
  HeapT xs' >>= f = HeapT (xs' >>= goH mempty)
    where
      goN i (Node k v xs) = liftA2 (\fv ys -> (ik <>* fv) <> ys) (runHeapT (f v)) (goF ik xs)
        where ik = i <> k

      goH _ Empty     = pure Empty
      goH i (Tree xs) = goN i xs

      goF _ Nil       = pure Empty
      goF i (x :- xs) = goF' i x xs

      goF' i x1 Nil = goN i =<< runNodeT x1
      goF' i x1 (x2 :- Nil) = liftA2 (<>) (goN i =<< runNodeT x1) (goN i =<< runNodeT x2)
      goF' i x1 (x2 :- x3 :- xs) = liftA2 (<>) (liftA2 (<>) (goN i =<< runNodeT x1) (goN i =<< runNodeT x2)) (goF' i x3 xs)

instance (Group a, Ord a, Monad m) => Applicative (NodeT a m) where
    pure x = NodeT (pure (Node mempty x Nil))
    (<*>) = ap

instance (Group a, Ord a, Monad m) => Monad (NodeT a m) where
    NodeT xs' >>= f = NodeT (xs' >>= goN mempty)
      where
        goN i (Node k v Nil) = fmap ((i <> k) <>!) (runNodeT (f v))
        goN i (Node k v (x :- xs)) = liftA2 (\fv ys -> (ik <>! fv) <> ys) (runNodeT (f v)) (goF ik x xs)
          where ik = i <> k

        goF i x1 Nil = goN i =<< runNodeT x1
        goF i x1 (x2 :- Nil) = liftA2 (<>) (goN i =<< runNodeT x1) (goN i =<< runNodeT x2)
        goF i x1 (x2 :- x3 :- xs) = liftA2 (<>) (liftA2 (<>) (goN i =<< runNodeT x1) (goN i =<< runNodeT x2)) (goF i x3 xs)

instance (Group a, Ord a, Applicative m) => Semigroup (HeapT a m b) where
    HeapT xs <> HeapT ys = HeapT (liftA2 (<>) xs ys)

instance (Group a, Ord a, Applicative m) => Monoid (HeapT a m b) where
    mempty = HeapT (pure Empty)
    mappend = (<>)

instance (Group a, Ord a, Monad m) => Alternative (HeapT a m) where
    (<|>) = (<>)
    empty = mempty

instance (Group a, Ord a, Monad m) => MonadPlus (HeapT a m) where

instance (Group a, Ord a, Applicative m) => Semigroup (NodeT a m b) where
    NodeT xs <> NodeT ys = NodeT (liftA2 (<>) xs ys)

instance Monoid a => MonadTrans (HeapT a) where
    lift xs = HeapT (fmap (\x -> Tree (Node mempty x Nil)) xs)

instance Monoid a => MonadTrans (NodeT a) where
    lift xs = NodeT (fmap (\x -> Node mempty x Nil) xs)

mapForest :: (NodeT a m b -> NodeT a' m' b') -> Forest a m b -> Forest a' m' b'
mapForest _ Nil       = Nil
mapForest f (x :- xs) = f x :- mapForest f xs

instance (Group a, Ord a, MonadReader r m) =>
         MonadReader r (NodeT a m) where
    ask = lift ask
    local k (NodeT m) =
        NodeT
            (fmap
                 (\(Node x xv xs) ->
                       Node x xv (mapForest (local k) xs))
                 (local k m))

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap
{-# INLINE (<&>) #-}

instance (Group a, Ord a, MonadReader r m) => MonadReader r (HeapT a m) where
    ask = lift ask
    local k (HeapT m) = HeapT (local k m <&> \case
                                    Empty -> Empty
                                    Tree (Node x xv xs) -> Tree (Node x xv (mapForest (local k) xs)))

instance (Ord a, Group a, MonadState s m) => MonadState s (HeapT a m) where
    get = lift get
    put x = lift (put x)
    state k = lift (state k)

instance (Ord a, Group a, MonadState s m) => MonadState s (NodeT a m) where
    get = lift get
    put x = lift (put x)
    state k = lift (state k)

instance (Group a, Ord a, MonadError e m) => MonadError e (HeapT a m) where
    throwError e = HeapT (throwError e)

    catchError (HeapT m) k = HeapT (catchError m (runHeapT . k))

instance (Group a, Ord a, MonadError e m) => MonadError e (NodeT a m) where
    throwError e = NodeT (throwError e)
    catchError (NodeT m) k = NodeT (catchError m (runNodeT . k))

prio :: Applicative m => a -> b -> HeapT a m b
prio x y = HeapT (pure (Tree (Node x y Nil)))
{-# INLINE prio #-}

mergeQs :: (Ord a, Group a, Applicative m) => Forest a m b -> HeapT a m b
mergeQs Nil = HeapT (pure Empty)
mergeQs (x :- xs) = HeapT (Tree <$> go x xs)
  where
    go t Nil = runNodeT t
    go t1 (t2 :- Nil) = liftA2 (<>) (runNodeT t1) (runNodeT t2)
    go t1 (t2 :- t3 :- ts) = liftA2 (<>) (liftA2 (<>) (runNodeT t1) (runNodeT t2)) (go t3 ts)

popMin :: (Ord a, Group a, Applicative m) => HeapT a m b -> m (Maybe ((a,b), HeapT a m b))
popMin (HeapT xs) = xs <&> \case
    Empty -> Nothing
    Tree (Node x y ys) -> Just ((x,y) , HeapT ((x <>*) <$> runHeapT (mergeQs ys)))
{-# INLINE popMin #-}
