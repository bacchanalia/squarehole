module Data.Type.Semigroup where

import GHC.TypeLits

-- | Type level Semigroup
type family (a :: k) <> (b :: k) :: k

type instance a <> b = AppendSymbol a b

type instance LT <> _r = LT
type instance EQ <> r  = r
type instance GT <> _r = GT
