{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-|
Module      : Data.Type.Map
Description : Type level weight balanced trees.
Copyright   : (c) Zoe Zuser, 2024
License     : BSD-3
Maintainer  : zmzuser@gmail.com
Stability   : experimental
Portability : GHC only

It's Data.Map. It's Data.Map at the type level.
It's Data.Map implemented specially to be at the type level.
Type level Data.Map.

Keys can be any type that has a type instance for 'Compare'.
-}
module Data.Type.Map
  {-
  ( -- * Construction
    Map(..)
  , Empty, Singleton
    -- ** From lists
  , FromList, FromList'
    -- * Families for higher-order operations
    -- * Operations on single elements
    -- ** Insertion
  , Insert, Insert'
    -- ** Update
  , Update
    -- ** Deletion
  , Delete, Delete'
    -- * Querying
    -- ** Boolean Operations
  , Member
    -- ** Lookup
  , Lookup, Lookup'
    -- ** Size
  , Size
    -- * Set-like Operations
  , Union, Intersection, Difference
    -- * Aggregate Operations
    -- ** Mapping
  , MapWithKey, MapWithKeyFun
    -- ** Folding
  , FoldrWithKey, FoldrWithKeyFun
    -- ** Filtering
  , FilterWithKey, FilterWithKeyFun
    -- * Conversion to List
  , ToList, Keys, Elems
    -- * Utilities for making Compare instances
  , type (<>)
  ) -} where

import Data.Kind
import Data.Proxy
import Data.Type.Bool
import Data.Type.Equality
import Data.Type.Ord
import GHC.TypeError
import GHC.TypeLits
import GHC.TypeNats

import Data.Type.Function
import Data.Type.Semigroup

------ Construction

-- | Type level balanced weighted binary trees.
-- It's Data.Map at the type level.
data Map k a = Tip | Bin Nat k a (Map k a) (Map k a)

-- | The empty map.
type Empty = Tip

-- | A single element map.
type Singleton k a = Bin 1 k a Tip Tip

-- | Operator version of Singleton
type k :-> a = Singleton k a

---- From lists

-- | Build a map from a list of key/value pairs.
-- If a key appears more than once, the key and values are combined using the
-- type instance of 'App3' indexed by 'f'.
type family FromListWithKey (f :: k_a_a_a) (xs :: [(k, a)]) :: Map k a where
  FromListWithKey f '[]          = Empty
  FromListWithKey f ('(k, x):xs) = InsertWithKey f k x (FromListWithKey f xs)

-- | Build a map from a list of key/value pairs.
-- It's a type error if the list has duplicate keys.
type family FromList (xs :: [(k, a)]) :: Map k a where
  FromList xs = FromListWithKey (Error (FromListErrMsg xs)) xs
type FromListErrMsg xs = Text "Data.Type.Map.FromList: duplicate keys in " :<>: ShowType xs

-- | Build a map from a list of key/value pairs.
-- If a key appears more than once, the values are combined using the
-- type instance of 'App2' indexed by 'f'.
type family FromListWith (f :: a_a_a) (xs :: [(k, a)]) :: Map k a where
  FromListWith f xs = FromListWithKey (ArgTail f) xs

------ Operations on single elements

type KeyInMapErrMsg    name k m = Text "Data.Type.Map." :<>: Text name :<>: Text ": key " :<>: ShowType k :<>: Text " already in " :<>: ShowType m
type KeyNotInMapErrMsg name k m = Text "Data.Type.Map." :<>: Text name :<>: Text ": key " :<>: ShowType k :<>: Text " not in "     :<>: ShowType m

---- Insertion

-- | Insert a key and value into the map.
-- If a key appears more than once, the key and values are combined using the
-- type instance of 'App3' indexed by 'f'.
type family InsertWithKey (f :: k_a_a_a) (key :: k) (val :: a) (map :: Map k a) :: Map k a where
  InsertWithKey f k x Tip               = Singleton k x
  InsertWithKey f k x (Bin s mk mx l r) = Compared k mk
    {- LT -} (BalanceL mk mx (InsertWithKey f k x l) r)
    {- EQ -} (Bin s k (App3 f k x mx) l r)
    {- GT -} (BalanceR mk mx l (InsertWithKey f k x r))

-- | Insert a key and value into the map.
-- It's a type error if the key is already in the map.
type family Insert (key :: k) (val :: a) (map :: Map k a) :: Map k a where
  Insert k x m = InsertWithKey (Error (KeyInMapErrMsg "Insert" k m)) k x m

-- | Insert a key and value into the map.
-- If a key appears more than once, the values are combined using the
-- type instance of 'App2' indexed by 'f'.
type family InsertWith (f :: a_a_a) (key :: k) (val :: a) (map :: Map k a) :: Map k a where
  InsertWith f k x m = InsertWithKey (ArgTail f) k x m

---- Deletion

type family Delete_ (notInMap :: Map k a) (key :: k) (map :: Map k a) :: Map k a where
  Delete_ z k Tip               = z
  Delete_ z k (Bin _s mk x l r) = Compared k mk
    {- LT -} (BalanceR mk x (Delete_ z k l) r)
    {- EQ -} (Glue l r)
    {- GT -} (BalanceL mk x l (Delete_ z k r))

-- | Delete a key from the map.
-- It's a type error if the key is not in the map.
type family Delete (key :: k) (map :: Map k a) :: Map k a where
  Delete k m = Delete_ (TypeError (KeyNotInMapErrMsg "Delete" k m)) k m

-- | Without deletes a key from the map if it is present,
-- and returns the original map otherwise
type family Without (key :: k) (map :: Map k a) :: Map k a where
  Without k m = Delete_ Tip k m

---- Update

type family AdjustWithKey_ (msg :: ErrorMessage) (f :: k_a_a) (key :: k) (map :: Map k a) :: Map k a where
  AdjustWithKey_ err f k Tip              = TypeError err
  AdjustWithKey_ err f k (Bin s mk x l r) = Compared k mk
    {- LT -} (Bin s mk x (AdjustWithKey_ err f k l) r)
    {- EQ -} (Bin s k (App2 f k x) l r)
    {- GT -} (Bin s mk x l (AdjustWithKey_ err f k r))

-- | Replaces the value at a specific key.
-- It's a type error if the key is not in the map.
type family Replace (key :: k) (val :: x) (map :: Map k a) :: Map k a where
  Replace k x m = AdjustWithKey_ (KeyNotInMapErrMsg "Replace" k m) (Const x) k m

-- | Updates the value of a specific key, using the type instance of 'App1' indexed by 'f'.
-- It's a type error if the key is not in the map.
type family Adjust (f :: a_a) (key :: k) (map :: Map k a) :: Map k a where
  Adjust f k m = AdjustWithKey_ (KeyNotInMapErrMsg "Adjust" k m) (ArgTail f) k m

-- | Updates the value of a specific key, combining it with the key using the
-- type instance of 'App2' indexed by 'f'
-- It's a type error if the key is not in the map.
type family AdjustWithKey (f :: k_a_a) (key :: k) (map :: Map k a) :: Map k a where
  AdjustWithKey f k m = AdjustWithKey_ (KeyNotInMapErrMsg "AdjustWithKey" k m) f k m

{-
type family UpdateWithKey_ (err :: ErrorMessage) (f :: k_a_Maybe_a) (key :: k) (map :: Map k a) :: Map k a where
  UpdateWithKey_ err f k Tip              = TypeError err
  UpdateWithKey_ err f k (Bin s mk x l r) = Compared k mk
    {- LT -} (BalanceR mk x (UpdateWithKey_ err f k l) r)
    {- EQ -} (CaseMaybe (App2 f k x)
                (Glue l r)
                )
    {- GT -} (BalanceL mk x l (UpdateWithKey_ err f k r))
-}

------ Querying

---- Membership

-- | Test if a key is in the map.
type family Member (key :: k) (map :: Map k a) :: Bool where
  Member k Tip              = False
  Member k (Bin s mk x l r) = Compared k mk
    {- LT -} (Member k l)
    {- EQ -} True
    {- GT -} (Member k r)

-- | Map membership as a constraint.
type k ! m = Assert (Member k m) (TypeError (MemberErrMsg k m) :: Constraint)
type MemberErrMsg k m = Text "Cannot satisfy: key " :<>: ShowType k :<>: Text " in " :<>: ShowType m

-- | Lookup the value associated with a key,
-- returning Nothing when the key is not present.
type family Lookup (key :: k) (map :: Map k a) :: Maybe a where
  Lookup _k Tip               = Nothing
  Lookup k  (Bin _s mk x l r) = Compared k mk
    {- LT -} (Lookup k l)
    {- EQ -} (Just x)
    {- GT -} (Lookup k r)

-- | Get the value associated with a key.
-- It's a type error if the key is not in the map.
type family Get (key :: k) (map :: Map k a) :: a where
  Get k m = CaseMaybe (Lookup k m) (TypeError (GetErrMsg k m)) Id
type GetErrMsg k m = Text "Data.Type.Map.Get: key " :<>: ShowType k :<>: Text " not in " :<>: ShowType m

---- Size

-- | The number of elements in the map.
type family Size (map :: Map k a) :: Nat where
  Size Tip             = 0
  Size (Bin s k x l r) = s

------ Set-like Operations

{-
-- | Left biased union.
type family Union (l :: Map k a) (r :: Map k a) :: Map k a where
  Union l r = FromList (ToList l ++ ToList r)

-- | Left biased intersection.
type family Intersection (l :: Map k a) (r :: Map k x) :: Map k a where
  Intersection l r = FromList (SortedAssocListIntersection (ToList l) (ToList r))

-- | Left biased difference.
type family Difference (l :: Map k a) (r :: Map k a) :: Map k a where
  Difference l r = FromList (SortedAssocListDifference (ToList l) (ToList r))
-}


------ Mapping/Folding/Filtering

---- Map


{-
type family MapWithKey (f :: ix) (m :: Map k a) :: Map k b where
  MapWithKey f Tip             = Tip
  MapWithKey f (Bin s k x l r) = Bin s k (MapWithKeyFun f k x) (MapWithKey f l) (MapWithKey f r)

type family MapWithKeyFun (f :: ix) (key :: k) (val :: x) :: b

type family FoldrWithKey (f :: ix) (z :: b) (m :: Map k a) :: b where
  FoldrWithKey f z Tip              = z
  FoldrWithKey f z (Bin _s k x l r) = FoldrWithKey f (FoldrWithKeyFun f k x (FoldrWithKey f z r)) l

type family FoldrWithKeyFun (f :: ix) (key :: k) (val :: x) (acc :: a) :: a

type family FilterWithKey (f :: ix) (m :: Map k a) :: Map k a where
  FilterWithKey f Tip             = Tip
  FilterWithKey f (Bin s k x l r) = If (FilterWithKeyFun f k x)
    (Link k x (FilterWithKey f l) (FilterWithKey f r))
    (Link2 (FilterWithKey f l) (FilterWithKey f r))

type family FilterWithKeyFun (f :: ix) (key :: k) (val :: x) :: Bool
-}

------ Conversion

{-
-- | Convert a map to sorted a list of key/value pairs.
type ToList (m :: Map k a) = FoldrWithKey ToListFun ('[] :: [(k, a)]) m
data ToListFun
type instance FoldrWithKeyFun ToListFun k a acc = ('(k, a) : acc)

-- | Get a sorted list of keys from a map.
type Keys (m :: Map k a) = FoldrWithKey KeysFun ('[] :: [k]) m
data KeysFun
type instance FoldrWithKeyFun KeysFun k _v acc = (k : acc)

-- | Get a list of elements in order of their keys from a map.
type Elems (m :: Map k a) = FoldrWithKey ElemsFun ('[] :: [a]) m
data ElemsFun
type instance FoldrWithKeyFun ElemsFun k x acc = (v : acc)
-}

------ Internal Implementation

type family Bin_ (key :: k) (val :: x) (l :: Map k a) (r :: Map k x) :: Map k x where
  Bin_ k x l r = Bin (1 + Size l + Size r) k x l r

---- Internals for: Insertion/Update/Deletion

type family BalanceL (key :: k) (val :: x) (l :: Map k a) (r :: Map k a) :: Map k a where
  BalanceL k x Tip Tip
    = Bin 1 k x Tip Tip

  BalanceL k x (Bin 1 lk lv Tip Tip) Tip
    = Bin 2 k x (Bin 1 lk lv Tip Tip) Tip

  BalanceL k x (Bin 2 lk lv Tip (Bin 1 lrk lrv Tip Tip)) Tip
    = Bin 3 lrk lrv (Bin 1 lk lv Tip Tip) (Bin 1 k x Tip Tip)

  BalanceL k x (Bin 2 lk lv ll Tip) Tip
    = Bin 3 lk lv ll (Bin 1 k x Tip Tip)

  BalanceL k x (Bin ls lk lv ll (Bin lrs lrk lrv lrl lrr)) Tip
    = If (Compare lrs (2 * Size ll) == LT)
        (Bin (ls + 1) lk lv ll (Bin (lrs + 1) k x (Bin lrs lrk lrv lrl lrr) Tip))
        (Bin (ls + 1) lrk lrv
          (Bin (Size ll + Size lrl + 1) lk lv ll lrl)
          (Bin (Size lrr + 1) k x lrr Tip))

  BalanceL k x Tip r
    = Bin (Size r + 1) k x Tip r

  BalanceL k x (Bin ls lk lv ll (Bin lrs lrk lrv lrl lrr)) r
    = If (Compare ls (2 * Size r) == GT)
        (If (Compare lrs (2 * Size ll) == LT)
          (Bin (ls + Size r + 1) lk lv ll (Bin (lrs + Size r + 1) k x (Bin lrs lrk lrv lrl lrr) r))
          (Bin (ls + Size r + 1) lrk lrv
            (Bin (Size ll + Size lrl + 1) lk lv ll lrl)
            (Bin (Size lrr + Size r + 1) k x lrr r)))
        (Bin (ls + Size r + 1) k x (Bin ls lk lv ll (Bin lrs lrk lrv lrl lrr)) r)

type family BalanceR (key :: k) (val :: x) (l :: Map k a) (r :: Map k a) :: Map k a where
  BalanceR k x Tip Tip
    = Bin 1 k x Tip Tip

  BalanceR k x Tip (Bin 1 rk rv Tip Tip)
    = Bin 2 k x Tip (Bin 1 rk rv Tip Tip)

  BalanceR k x Tip (Bin 2 rk rv Tip rr)
    = Bin 3 rk rv (Bin 1 k x Tip Tip) rr

  BalanceR k x Tip (Bin 2 rk rv (Bin 1 rlk rlv Tip Tip) Tip)
    = Bin 3 rlk rlv (Bin 1 k x Tip Tip) (Bin 1 rk rv Tip Tip)

  BalanceR k x Tip (Bin rs rk rv (Bin rls rlk rlv rll rlr) rr)
    = If (Compare rls (2 * Size rr) == LT)
        (Bin (rs + 1) rk rv (Bin (rls + 1) k x Tip (Bin rls rlk rlv rll rlr)) rr)
        (Bin (rs + 1) rlk rlv
          (Bin (Size rll + 1) k x Tip rll)
          (Bin (Size rlr + Size rr + 1) rk rv rlr rr))

  BalanceR k x l Tip
    = Bin (Size l + 1) k x l Tip

  BalanceR k x l (Bin rs rk rv (Bin rls rlk rlv rll rlr) rr)
    = If (Compare rs (2 * Size l) == GT)
        (If (Compare rls (2 * Size rr) == LT)
          (Bin (Size l + rs + 1) rk rv (Bin (Size l + rls + 1) k x l (Bin rls rlk rlv rll rlr)) rr)
          (Bin (Size l + rs + 1) rlk rlv
            (Bin (Size l + Size rll + 1) k x l rll)
            (Bin (Size rlr + Size rr + 1) rk rv rlr rr)))
        (Bin (Size l + rs + 1) k x l (Bin rs rk rv (Bin rls rlk rlv rll rlr) rr))

type family Glue (l :: Map k a) (r :: Map k a) :: Map k a where
  Glue Tip                  Tip                  = Tip
  Glue Tip                  r                    = r
  Glue l                    Tip                  = l
  Glue (Bin ls lk lv ll lr) (Bin rs rk rv rl rr) = If (Compare ls rs == GT)
    (GlueR (MaxViewSure lk lv ll lr) (Bin rs rk rv rl rr))
    (GlueL (Bin ls lk lv ll lr) (MinViewSure rk rv rl rr))

data View k x = View k x (Map k x)

type family GlueR (l :: View k x) (r :: Map k a) :: Map k a where
  GlueR ('View k x l) r = BalanceR k x l r

type family GlueL (l :: Map k a) (r :: View k x) :: Map k a where
  GlueL l ('View k x r) = BalanceL k x l r

type family MaxViewSure (key :: k) (val :: x) (l :: Map k a) (r :: Map k a) :: View k x where
  MaxViewSure k x l Tip                  = 'View k x l
  MaxViewSure k x l (Bin _s rk rv rl rr) = MaxViewSure_ k x l (MaxViewSure rk rv rl rr)

type family MaxViewSure_ (key :: k) (val :: x) (l :: Map k a) (view :: View k x) :: View k x where
  MaxViewSure_ k x l ('View km vm r) = 'View km vm (BalanceL k x l r)

type family MinViewSure (key :: k) (val :: x) (l :: Map k a) (r :: Map k a) :: View k x where
  MinViewSure k x Tip                  r = 'View k x r
  MinViewSure k x (Bin _s lk lv ll lr) r = MinViewSure_ k x (MinViewSure lk lv ll lr) r

type family MinViewSure_ (key :: k) (val :: x) (view :: View k x) (r :: Map k a) :: View k x where
  MinViewSure_ k x ('View km vm l) r = 'View km vm (BalanceL k x l r)

---- Internal for: Mapping/Folding/Filtering

type family Link (key :: k) (val :: x) (l :: Map k a) (r :: Map k a) :: Map k a where
  Link k x Tip                  r                    = InsertMin k x r
  Link k x l                    Tip                  = InsertMax k x l
  Link k x (Bin ls lk lv ll lr) (Bin rs rk rv rl rr) =
    If (Compare (3 * ls) rs == LT) (BalanceL rk rv (Link k x (Bin ls lk lv ll lr) rl) rr) (
    If (Compare (3 * rs) ls == LT) (BalanceR lk lv ll (Link k x lr (Bin rs rk rv rl rr))) (
    {- Otherwise #-}               (Bin (ls + rs + 1) k x (Bin ls lk lv ll lr) (Bin rs rk rv rl rr))))

type family Link2 (l :: Map k a) (r :: Map k a) :: Map k a where
  Link2 Tip r   = r
  Link2 l   Tip = l
  Link2 (Bin ls lk lv ll lr) (Bin rs rk rv rl rr) =
    If (Compare (3 * ls) rs == LT) (BalanceL rk rv (Link2 (Bin ls lk lv ll lr) rl) rr) (
    If (Compare (3 * rs) ls == LT) (BalanceR lk lv ll (Link2 lr (Bin rs rk rv rl rr))) (
    {- Otherwise #-}               (Glue (Bin ls lk lv ll lr) (Bin rs rk rv rl rr))))

type family InsertMin (key :: k) (val :: x) (m :: Map k a) :: Map k a where
  InsertMin k x Tip                = Singleton k x
  InsertMin k x (Bin _s mk mx l r) = BalanceL mk mx (InsertMin k x l) r

type family InsertMax (key :: k) (val :: x) (m :: Map k a) :: Map k a where
  InsertMax k x Tip                = Singleton k x
  InsertMax k x (Bin _s mk mx l r) = BalanceR mk mx l (InsertMax k x r)

---- Internal for: Set-like Operations

type family (xs :: [k]) ++ (ys :: [k]) :: [k] where
  '[] ++ ys    = ys
  (x:xs) ++ ys = x : (xs ++ ys)

type family SortedAssocListIntersection (xs :: [(Symbol, a)]) (ys :: [(Symbol, b)]) :: [(Symbol, a)] where
  SortedAssocListIntersection '[]           ys            = '[]
  SortedAssocListIntersection xs            '[]           = '[]
  SortedAssocListIntersection ('(xk,xv):xs) ('(yk,yv):ys) = Compared xk yk
    {- LT -} (SortedAssocListIntersection xs ('(yk,yv):ys))
    {- EQ -} ('(xk,xv) : SortedAssocListIntersection xs ys)
    {- GT -} (SortedAssocListIntersection ('(xk,xv):xs) ys)

type family SortedAssocListDifference (xs :: [(Symbol, a)]) (ys :: [(Symbol, b)]) :: [(Symbol, a)] where
  SortedAssocListDifference '[]           _ys           = '[]
  SortedAssocListDifference xs            '[]           = xs
  SortedAssocListDifference ('(xk,xv):xs) ('(yk,yv):ys) = Compared xk yk
    {- LT -} ('(xk,xv) : SortedAssocListDifference xs ('(yk,yv):ys))
    {- EQ -} (SortedAssocListDifference xs ys)
    {- GT -} (SortedAssocListDifference ('(xk,xv):xs) ys)
