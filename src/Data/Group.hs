------------------------------------------------------------------------
-- |
-- Module      : Data.Group
-- Copyright   : Donnacha Oisín Kidney 2019
-- License     : Apache 2.0
-- Portability : GHC
module Data.Group where

import Data.Monoid

-- | A group satisfies the axioms:
--
-- @x '<>' 'inv' x = 'mempty'@
--
-- @'inv' x '<>' x = 'mempty'@
class Monoid a => Group a where
    inv :: a -> a

instance Num a => Group (Sum a) where
    inv (Sum x) = Sum (negate x)
