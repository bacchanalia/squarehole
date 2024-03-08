{-# OPTIONS_GHC -fno-warn-orphans #-}
{-|
Module      : Data.Type.Ord.Instances
Description : Orphan type family instances for Data.Type.Ord.Compare
Copyright   : (c) Zoe Zuser, 2024
License     : BSD-3
Maintainer  : zmzuser@gmail.com
Stability   : experimental
Portability : GHC only
-}

module Data.Type.Ord.Instances where

import Data.Type.Ord

import Data.Type.Semigroup

type instance Compare () () = EQ
type instance Compare '(a1, a2) '(b1, b2) = Compare a1 b1 <> Compare a2 b2
type instance Compare '(a1, a2, a3) '(b1, b2, b3) = Compare a1 b1 <> Compare a2 b2 <> Compare a3 b3

type instance Compare False True  = LT
type instance Compare False False = EQ
type instance Compare True  False = GT
type instance Compare True  True  = EQ

type instance Compare (Nothing :: Maybe k) (Nothing :: Maybe k) = EQ
type instance Compare (Nothing :: Maybe k) (Just _b :: Maybe k) = LT
type instance Compare (Just _a :: Maybe k) (Nothing :: Maybe k) = GT
type instance Compare (Just a  :: Maybe k) (Just b  :: Maybe k) = Compare a b

type instance Compare (Left   a :: Either l r) (Left   b :: Either l r) = Compare a b
type instance Compare (Left  _a :: Either l r) (Right _b :: Either l r) = LT
type instance Compare (Right  a :: Either l r) (Left  _b :: Either l r) = GT
type instance Compare (Right  a :: Either l r) (Right  b :: Either l r) = Compare a b
