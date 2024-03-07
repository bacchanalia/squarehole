{-|
Module      : Data.Map.TypeLevel
Description : Type level weight balanced trees.
Copyright   : (c) Zoe Zuser, 2024
License     : BSD-3
Maintainer  : zmzuser@gmail.com
Stability   : experimental
Portability : GHC only

It's Data.Map at the type level.
Type level Data.Map.
Data.Map in your types.

Keys can be any type that has a type instance for 'Compare'.
-}
module Data.Type.Map
  ( -- * Construction
    Map(..)
  , Empty, Singleton
    -- ** From Lists
  , FromList, FromList'
    -- * Inserting / Updating / Deleting
  , Insert, Insert', Update, Delete, Delete'
    -- * Querying
  , Member, Lookup, Lookup', Size
    -- * Binary set-like operations
  , Union, Intersection, Difference
    -- * Folding, Mapping, Filtering
  , FoldrWithKey, FoldrWithKeyFun
  , MapWithKey, MapWithKeyFun
  , FilterWithKey, FilterWithKeyFun
    -- * Conversion
  , ToList, Keys, Elems
    -- * Utilities for making Compare instances
  , type (<>)
  ) where

import Data.Type.Bool
import Data.Type.Equality
import Data.Type.Ord
import GHC.TypeNats
import GHC.TypeLits
import Data.Proxy

-- | Type level balanced weighted binary trees.
-- It's Data.Map at the type level.
data Map k v = Tip | Bin Nat k v (Map k v) (Map k v)

------ Construction

-- | The empty map.
type Empty = Tip

-- | A single element map.
type Singleton k v = Bin 1 k v Tip Tip

---- From Lists

-- | Build a map from a list of key/value pairs.
-- It's a type error if the list has duplicate keys.
type family FromList (xs :: [(k, v)]) :: Map k v where
  FromList '[]          = Empty
  FromList ('(k, v):xs) = Insert k v (FromList xs)

-- | Build a map from a list of key/value pairs.
-- Use the first value when given duplicate keys.
-- Note: This behaviour differs from Data.Map
type family FromList' (xs :: [(k, v)]) :: Map k v where
  FromList' '[]          = Empty
  FromList' ('(k, v):xs) = Insert' k v (FromList' xs)

------ Inserting / Updating / Deleting

-- | Insert a key and value into the map.
-- It's a type error if the key is already in the map.
type family Insert (key :: k) (val :: v) (m :: Map k v) :: Map k v where
  Insert k v Tip               = Singleton k v
  Insert k v (Bin s mk mv l r) = OrdCond (Compare k mk)
    {- LT -} (BalanceL mk mv (Insert k v l) r)
    {- EQ -} (TypeError (Text "Data.Type.Map.Insert: duplicate key"))
    {- GT -} (BalanceR mk mv l (Insert k v r))

-- | Insert a key and value into the map.
-- If the key is already in the map, replace it's value.
type family Insert' (key :: k) (val :: v) (m :: Map k v) :: Map k v where
  Insert' k v Tip               = Singleton k v
  Insert' k v (Bin s mk mv l r) = OrdCond (Compare k mk)
    {- LT -} (BalanceL mk mv (Insert' k v l) r)
    {- EQ -} (Bin s k v l r)
    {- GT -} (BalanceR mk mv l (Insert' k v r))

-- | Update a key that is already in the map with a new value.
-- It's a type error if the key is not in the map.
type family Update (key :: k) (val :: v) (m :: Map k v) :: Map k v where
  Update k v Tip               = TypeError (Text "Data.Type.Map.Update: key not in map")
  Update k v (Bin s mk mv l r) = OrdCond (Compare k mk)
    {- LT -} (Bin s mk mv (Update k v l) r)
    {- EQ -} (Bin s k v l r)
    {- GT -} (Bin s mk mv l (Update k v r))

-- | Delete a key from the map.
-- It's a type error if the key is not in the map.
type family Delete (key :: k) (m :: Map k v) :: Map k v where
  Delete k Tip               = TypeError (Text "Data.Type.Map.Delete: key not in map")
  Delete k (Bin _s mk v l r) = OrdCond (Compare k mk)
    {- LT -} (BalanceR mk v (Delete' k l) r)
    {- EQ -} (Glue l r)
    {- GT -} (BalanceL mk v l (Delete' k r))

-- | Delete a key from the map.
-- Return the original map if the key is not present.
type family Delete' (key :: k) (m :: Map k v) :: Map k v where
  Delete' _k Tip             = Tip
  Delete' k (Bin _s mk v l r) = OrdCond (Compare k mk)
    {- LT -} (BalanceR mk v (Delete' k l) r)
    {- EQ -} (Glue l r)
    {- GT -} (BalanceL mk v l (Delete' k r))

------ Querying

-- | Test if a key is in the map.
type family Member (key :: k) (m :: Map k v) :: Bool where
  Member k Tip                = False
  Member k (Bin _s mk _v l r) = OrdCond (Compare k mk)
    {- LT -} (Member k l)
    {- EQ -} True
    {- GT -} (Member k r)

-- | Map membership as a constraint.
class (Member key m ~ True) => (key :: k) ! (m :: Map k v)
instance (Member key m ~ True) => (key :: k) ! (m :: Map k v)

-- | Lookup the value associated with a key.
-- It's a type error if the key is not in the map.
type family Lookup (key :: k) (m :: Map k v) :: v where
  Lookup k Tip               = TypeError (Text "Data.Type.Map.Lookup: key not in map")
  Lookup k (Bin _s mk v l r) = OrdCond (Compare k mk)
    {- LT -} (Lookup k l)
    {- EQ -} v
    {- GT -} (Lookup k r)

-- | Lookup the value associated with a key.
-- Returns (Just a) if the key is in the map and Nothing otherwise.
type family Lookup' (key :: k) (m :: Map k v) :: Maybe v where
  Lookup' _k Tip               = Nothing
  Lookup' k  (Bin _s mk v l r) = OrdCond (Compare k mk)
    {- LT -} (Lookup' k l)
    {- EQ -} (Just v)
    {- GT -} (Lookup' k r)

-- | The number of elements in the map.
type family Size (m :: Map k v) :: Nat where
  Size Tip                 = 0
  Size (Bin s _k _v _l _r) = s

------ Binary set-like operations

-- | Left biased union.
type family Union (l :: Map k v) (r :: Map k v) :: Map k v where
  Union l r = FromList (ToList l ++ ToList r)

-- | Left biased intersection.
type family Intersection (l :: Map k v) (r :: Map k x) :: Map k v where
  Intersection l r = FromList (SortedAssocListIntersection (ToList l) (ToList r))

-- | Left biased difference.
type family Difference (l :: Map k v) (r :: Map k v) :: Map k v where
  Difference l r = FromList (SortedAssocListDifference (ToList l) (ToList r))

------ Folding, Mapping, Filtering

type family FoldrWithKey (f :: ix) (z :: b) (m :: Map k a) :: b where
  FoldrWithKey f z Tip              = z
  FoldrWithKey f z (Bin _s k v l r) = FoldrWithKey f (FoldrWithKeyFun f k v (FoldrWithKey f z r)) l

type family FoldrWithKeyFun (f :: ix) (key :: k) (val :: v) (acc :: a) :: a

type family MapWithKey (f :: ix) (m :: Map k a) :: Map k b where
  MapWithKey f Tip             = Tip
  MapWithKey f (Bin s k v l r) = Bin s k (MapWithKeyFun f k v) (MapWithKey f l) (MapWithKey f r)

type family MapWithKeyFun (f :: ix) (key :: k) (val :: v) :: b

type family FilterWithKey (f :: ix) (m :: Map k a) :: Map k a where
  FilterWithKey f Tip             = Tip
  FilterWithKey f (Bin s k v l r) = If (FilterWithKeyFun f k v)
    (Link k v (FilterWithKey f l) (FilterWithKey f r))
    (Link2 (FilterWithKey f l) (FilterWithKey f r))

type family FilterWithKeyFun (f :: ix) (key :: k) (val :: v) :: Bool

------ Conversion

-- | Convert a map to sorted a list of key/value pairs.
type ToList (m :: Map k v) = FoldrWithKey ToListFun ('[] :: [(k, v)]) m
data ToListFun
type instance FoldrWithKeyFun ToListFun k v acc = ('(k, v) : acc)

-- | Get a sorted list of keys from a map.
type Keys (m :: Map k v) = FoldrWithKey KeysFun ('[] :: [k]) m
data KeysFun
type instance FoldrWithKeyFun KeysFun k _v acc = (k : acc)

-- | Get a list of elements in order of their keys from a map.
type Elems (m :: Map k v) = FoldrWithKey ElemsFun ('[] :: [v]) m
data ElemsFun
type instance FoldrWithKeyFun ElemsFun k v acc = (v : acc)

------ Utilities for making Compare instances

-- | Type level Semigroup instance for Ordering
type family (a :: k) <> (b :: k) :: k
type instance LT <> _r = LT
type instance EQ <> r  = r
type instance GT <> _r = GT

------ Internal Implementation

---- Internals for: Inserting / Updating / Deleting

type family BalanceL (key :: k) (val :: v) (l :: Map k v) (r :: Map k v) :: Map k v where
  BalanceL k v Tip Tip
    = Bin 1 k v Tip Tip

  BalanceL k v (Bin 1 lk lv Tip Tip) Tip
    = Bin 2 k v (Bin 1 lk lv Tip Tip) Tip

  BalanceL k v (Bin 2 lk lv Tip (Bin 1 lrk lrv Tip Tip)) Tip
    = Bin 3 lrk lrv (Bin 1 lk lv Tip Tip) (Bin 1 k v Tip Tip)

  BalanceL k v (Bin 2 lk lv ll Tip) Tip
    = Bin 3 lk lv ll (Bin 1 k v Tip Tip)

  BalanceL k v (Bin ls lk lv ll (Bin lrs lrk lrv lrl lrr)) Tip
    = If (Compare lrs (2 * Size ll) == LT)
        (Bin (ls + 1) lk lv ll (Bin (lrs + 1) k v (Bin lrs lrk lrv lrl lrr) Tip))
        (Bin (ls + 1) lrk lrv
          (Bin (Size ll + Size lrl + 1) lk lv ll lrl)
          (Bin (Size lrr + 1) k v lrr Tip))

  BalanceL k v Tip r
    = Bin (Size r + 1) k v Tip r

  BalanceL k v (Bin ls lk lv ll (Bin lrs lrk lrv lrl lrr)) r
    = If (Compare ls (2 * Size r) == GT)
        (If (Compare lrs (2 * Size ll) == LT)
          (Bin (ls + Size r + 1) lk lv ll (Bin (lrs + Size r + 1) k v (Bin lrs lrk lrv lrl lrr) r))
          (Bin (ls + Size r + 1) lrk lrv
            (Bin (Size ll + Size lrl + 1) lk lv ll lrl)
            (Bin (Size lrr + Size r + 1) k v lrr r)))
        (Bin (ls + Size r + 1) k v (Bin ls lk lv ll (Bin lrs lrk lrv lrl lrr)) r)

type family BalanceR (key :: k) (val :: v) (l :: Map k v) (r :: Map k v) :: Map k v where
  BalanceR k v Tip Tip
    = Bin 1 k v Tip Tip

  BalanceR k v Tip (Bin 1 rk rv Tip Tip)
    = Bin 2 k v Tip (Bin 1 rk rv Tip Tip)

  BalanceR k v Tip (Bin 2 rk rv Tip rr)
    = Bin 3 rk rv (Bin 1 k v Tip Tip) rr

  BalanceR k v Tip (Bin 2 rk rv (Bin 1 rlk rlv Tip Tip) Tip)
    = Bin 3 rlk rlv (Bin 1 k v Tip Tip) (Bin 1 rk rv Tip Tip)

  BalanceR k v Tip (Bin rs rk rv (Bin rls rlk rlv rll rlr) rr)
    = If (Compare rls (2 * Size rr) == LT)
        (Bin (rs + 1) rk rv (Bin (rls + 1) k v Tip (Bin rls rlk rlv rll rlr)) rr)
        (Bin (rs + 1) rlk rlv
          (Bin (Size rll + 1) k v Tip rll)
          (Bin (Size rlr + Size rr + 1) rk rv rlr rr))

  BalanceR k v l Tip
    = Bin (Size l + 1) k v l Tip

  BalanceR k v l (Bin rs rk rv (Bin rls rlk rlv rll rlr) rr)
    = If (Compare rs (2 * Size l) == GT)
        (If (Compare rls (2 * Size rr) == LT)
          (Bin (Size l + rs + 1) rk rv (Bin (Size l + rls + 1) k v l (Bin rls rlk rlv rll rlr)) rr)
          (Bin (Size l + rs + 1) rlk rlv
            (Bin (Size l + Size rll + 1) k v l rll)
            (Bin (Size rlr + Size rr + 1) rk rv rlr rr)))
        (Bin (Size l + rs + 1) k v l (Bin rs rk rv (Bin rls rlk rlv rll rlr) rr))

type family Glue (l :: Map k v) (r :: Map k v) :: Map k v where
  Glue Tip                  Tip                  = Tip
  Glue Tip                  r                     = r
  Glue l                     Tip                  = l
  Glue (Bin ls lk lv ll lr) (Bin rs rk rv rl rr) = If (Compare ls rs == GT)
    (GlueR (MaxViewSure lk lv ll lr) (Bin rs rk rv rl rr))
    (GlueL (Bin ls lk lv ll lr) (MinViewSure rk rv rl rr))

data View k v = View k v (Map k v)

type family GlueR (l :: View k v) (r :: Map k v) :: Map k v where
  GlueR ('View k v l) r = BalanceR k v l r

type family GlueL (l :: Map k v) (r :: View k v) :: Map k v where
  GlueL l ('View k v r) = BalanceL k v l r

type family MaxViewSure (key :: k) (val :: v) (l :: Map k v) (r :: Map k v) :: View k v where
  MaxViewSure k v l Tip                  = 'View k v l
  MaxViewSure k v l (Bin _s rk rv rl rr) = MaxViewSure_ k v l (MaxViewSure rk rv rl rr)

type family MaxViewSure_ (key :: k) (val :: v) (l :: Map k v) (view :: View k v) :: View k v where
  MaxViewSure_ k v l ('View km vm r) = 'View km vm (BalanceL k v l r)

type family MinViewSure (key :: k) (val :: v) (l :: Map k v) (r :: Map k v) :: View k v where
  MinViewSure k v Tip                  r = 'View k v r
  MinViewSure k v (Bin _s lk lv ll lr) r = MinViewSure_ k v (MinViewSure lk lv ll lr) r

type family MinViewSure_ (key :: k) (val :: v) (view :: View k v) (r :: Map k v) :: View k v where
  MinViewSure_ k v ('View km vm l) r = 'View km vm (BalanceL k v l r)

---- Internal for: Folding, Mapping, Filtering

type family Link (key :: k) (val :: v) (l :: Map k v) (r :: Map k v) :: Map k v where
  Link k v Tip                  r                    = InsertMin k v r
  Link k v l                    Tip                  = InsertMax k v l
  Link k v (Bin ls lk lv ll lr) (Bin rs rk rv rl rr) =
    If (Compare (3 * ls) rs == LT) (BalanceL rk rv (Link k v (Bin ls lk lv ll lr) rl) rr) (
    If (Compare (3 * rs) ls == LT) (BalanceR lk lv ll (Link k v lr (Bin rs rk rv rl rr))) (
    {- Otherwise #-}               (Bin (ls + rs + 1) k v (Bin ls lk lv ll lr) (Bin rs rk rv rl rr))))

type family Link2 (l :: Map k v) (r :: Map k v) :: Map k v where
  Link2 Tip r   = r
  Link2 l   Tip = l
  Link2 (Bin ls lk lv ll lr) (Bin rs rk rv rl rr) =
    If (Compare (3 * ls) rs == LT) (BalanceL rk rv (Link2 (Bin ls lk lv ll lr) rl) rr) (
    If (Compare (3 * rs) ls == LT) (BalanceR lk lv ll (Link2 lr (Bin rs rk rv rl rr))) (
    {- Otherwise #-}               (Glue (Bin ls lk lv ll lr) (Bin rs rk rv rl rr))))

type family InsertMin (key :: k) (val :: v) (m :: Map k v) :: Map k v where
  InsertMin k v Tip                = Singleton k v
  InsertMin k v (Bin _s mk mv l r) = BalanceL mk mv (InsertMin k v l) r

type family InsertMax (key :: k) (val :: v) (m :: Map k v) :: Map k v where
  InsertMax k v Tip                = Singleton k v
  InsertMax k v (Bin _s mk mv l r) = BalanceR mk mv l (InsertMax k v r)

---- Internal for: Binary set-like operations

type family (xs :: [k]) ++ (ys :: [k]) :: [k] where
  '[] ++ ys    = ys
  (x:xs) ++ ys = x : (xs ++ ys)

type family SortedAssocListIntersection (xs :: [(Symbol, a)]) (ys :: [(Symbol, b)]) :: [(Symbol, a)] where
  SortedAssocListIntersection '[]           ys            = '[]
  SortedAssocListIntersection xs            '[]           = '[]
  SortedAssocListIntersection ('(xk,xv):xs) ('(yk,yv):ys) = OrdCond (Compare xk yk)
    {- LT -} (SortedAssocListIntersection xs ('(yk,yv):ys))
    {- EQ -} ('(xk,xv) : SortedAssocListIntersection xs ys)
    {- GT -} (SortedAssocListIntersection ('(xk,xv):xs) ys)

type family SortedAssocListDifference (xs :: [(Symbol, a)]) (ys :: [(Symbol, b)]) :: [(Symbol, a)] where
  SortedAssocListDifference '[]           _ys           = '[]
  SortedAssocListDifference xs            '[]           = xs
  SortedAssocListDifference ('(xk,xv):xs) ('(yk,yv):ys) = OrdCond (Compare xk yk)
    {- LT -} ('(xk,xv) : SortedAssocListDifference xs ('(yk,yv):ys))
    {- EQ -} (SortedAssocListDifference xs ys)
    {- GT -} (SortedAssocListDifference ('(xk,xv):xs) ys)
