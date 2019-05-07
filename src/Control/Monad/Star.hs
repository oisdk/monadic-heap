module Control.Monad.Star where

import Control.Monad
import Control.Applicative
import Control.Monad.State

class MonadPlus m => MonadStar m where
    star :: (a -> m a) -> a -> m a
    plus :: (a -> m a) -> a -> m a
    star f x = pure x <|> plus f x
    plus f x = f x >>= star f

instance MonadStar m
      => MonadStar (StateT s m) where
    star f x =
      StateT
        (star (uncurry (runStateT . f)) . (,) x)
