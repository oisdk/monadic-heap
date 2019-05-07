------------------------------------------------------------------------
-- |
-- Module      : Data.Heap.Monadic.Internal
-- Copyright   : Donnacha Oisín Kidney 2019
-- License     : Apache 2.0
-- Portability : GHC
--
-- = Monadic Heaps
--
-- This module provides a pairing heap data structure with a monad
-- instance.

module Data.Heap.Monadic
  (Heap
  ,prio
  ,Group(..)
  ,popMin
  ,prios
  ,fromList
  ,fromListWith
  ,ordPrios
  )
  where

import Data.Group
import Data.Heap.Monadic.Internal
