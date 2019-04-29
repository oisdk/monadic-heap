module Data.Group where

import Data.Monoid

class Monoid a => Group a where
    inv :: a -> a

instance Num a => Group (Sum a) where
    inv (Sum x) = Sum (negate x)
