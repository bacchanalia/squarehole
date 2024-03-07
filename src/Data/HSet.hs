module Data.HSet where

import Prelude hiding (lookup, map, null)
import Data.Kind (Constraint)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as Map
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy(..))
import GHC.Prim (coerce)
import Type.Reflection (SomeTypeRep, Typeable, someTypeRep)
import Unsafe.Coerce (unsafeCoerce)
import Text.Show
import Data.Functor.Identity
import Data.Hashable
import GHC.TypeNats
import GHC.TypeLits

data SMap a = STip | SBin Nat Symbol a (SMap a) (SMap a)

type SMapEmpty = STip
type SMapSingleton k v = SBin 1 k v STip STip

type family SMapSize (m :: SMap a) :: Nat where
  SMapSize STip                 = 0
  SMapSize (SBin s _k _v _l _r) = s

type family SMapMember (k :: Symbol) (m :: SMap a) :: Bool where
  SMapMember k STip                = False
  SMapMember k (SBin _s mk _v l r) = CaseCmp (CmpSymbol k mk)
    {- LT -} (SMapMember k l)
    {- EQ -} True
    {- GT -} (SMapMember k r)

type family SMapLookup (k :: Symbol) (m :: SMap a) :: Maybe a where
  SMapLookup _k STip               = Nothing
  SMapLookup k  (SBin _s mk v l r) = CaseCmp (CmpSymbol k mk)
    {- LT -} (SMapLookup k l)
    {- EQ -} (Just v)
    {- GT -} (SMapLookup k r)

type family SMapLookup' (k :: Symbol) (m :: SMap a) :: a where
  SMapLookup' k  (SBin _s mk v l r) = CaseCmp (CmpSymbol k mk)
    {- LT -} (SMapLookup' k l)
    {- EQ -} v
    {- GT -} (SMapLookup' k r)

type family SMapInsert (k :: Symbol) (v :: a) (m :: SMap a) :: SMap a where
  SMapInsert k v STip               = SMapSingleton k v
  SMapInsert k v (SBin s mk mv l r) = CaseCmp (CmpSymbol k mk)
    {- LT -} (SMapBalanceL mk mv (SMapInsert k v l) r)
    {- EQ -} (SBin s k v l r)
    {- GT -} (SMapBalanceR mk mv l (SMapInsert k v r))

type family SMapInsert' (k :: Symbol) (v :: a) (m :: SMap a) :: SMap a where
  SMapInsert' k v STip               = SMapSingleton k v
  SMapInsert' k v (SBin s mk mv l r) = CaseCmpNE (CmpSymbol k mk)
    {- LT -} (SMapBalanceL mk mv (SMapInsert k v l) r)
    {- GT -} (SMapBalanceR mk mv l (SMapInsert k v r))

type family SMapFromList (xs :: [(Symbol, a)]) :: SMap a where
  SMapFromList '[]          = SMapEmpty
  SMapFromList ('(k, v):xs) = SMapInsert k v (SMapFromList xs)

type family SMapFromList' (xs :: [(Symbol, a)]) :: SMap a where
  SMapFromList' '[]          = SMapEmpty
  SMapFromList' ('(k, v):xs) = SMapInsert' k v (SMapFromList' xs)

type family SMapToList (m :: SMap a) :: [(Symbol, a)] where
  SMapToList STip              = '[]
  SMapToList (SBin _s k v l r) = SMapToList l ++ '[ '(k, v)] ++ SMapToList r

type family SMapKeys (m :: SMap a) :: [Symbol] where
  SMapKeys STip               = '[]
  SMapKeys (SBin _s k _v l r) = SMapKeys l ++ '[k] ++ SMapKeys r

type family SMapElems (m :: SMap a) :: [Symbol] where
  SMapElems STip               = '[]
  SMapElems (SBin _s _k v l r) = SMapElems l ++ '[v] ++ SMapElems r

type family SMapUnion (l :: SMap a) (r :: SMap a) :: SMap a where
  SMapUnion l r = SMapFromList (SMapToList l ++ SMapToList r)

type family SMapDelete (k :: Symbol) (m :: SMap a) :: SMap a where
  SMapDelete _k STip             = STip
  SMapDelete k (SBin _s mk v l r) = CaseCmp (CmpSymbol k mk)
    {- LT -} (SMapBalanceR mk v (SMapDelete k l) r)
    {- EQ -} (SMapGlue l r)
    {- GT -} (SMapBalanceL mk v l (SMapDelete k r))

type family SMapDelete' (k :: Symbol) (m :: SMap a) :: SMap a where
  SMapDelete' k (SBin _s mk v l r) = CaseCmp (CmpSymbol k mk)
    {- LT -} (SMapBalanceR mk v (SMapDelete k l) r)
    {- EQ -} (SMapGlue l r)
    {- GT -} (SMapBalanceL mk v l (SMapDelete k r))

-- intersection
-- difference

type family SMapBalanceL (k :: Symbol) (v :: Type) (l :: SMap a) (r :: SMap a) :: SMap a where
  SMapBalanceL k v STip STip
    = SBin 1 k v STip STip

  SMapBalanceL k v (SBin 1 lk lv STip STip) STip
    = SBin 2 k v (SBin 1 lk lv STip STip) STip

  SMapBalanceL k v (SBin 2 lk lv STip (SBin 1 lrk lrv STip STip)) STip
    = SBin 3 lrk lrv (SBin 1 lk lv STip STip) (SBin 1 k v STip STip)

  SMapBalanceL k v (SBin 2 lk lv ll STip) STip
    = SBin 3 lk lv ll (SBin 1 k v STip STip)

  SMapBalanceL k v (SBin ls lk lv ll (SBin lrs lrk lrv lrl lrr)) STip
    = If (CmpNat lrs (2 * SMapSize ll) == LT)
        (SBin (ls + 1) lk lv ll (SBin (lrs + 1) k v (SBin lrs lrk lrv lrl lrr) STip))
        (SBin (ls + 1) lrk lrv
          (SBin (SMapSize ll + SMapSize lrl + 1) lk lv ll lrl)
          (SBin (SMapSize lrr + 1) k v lrr STip))

  SMapBalanceL k v STip r
    = SBin (SMapSize r + 1) k v STip r

  SMapBalanceL k v (SBin ls lk lv ll (SBin lrs lrk lrv lrl lrr)) r
    = If (CmpNat ls (2 * SMapSize r) == GT)
        (If (CmpNat lrs (2 * SMapSize ll) == LT)
          (SBin (ls + SMapSize r + 1) lk lv ll (SBin (lrs + SMapSize r + 1) k v (SBin lrs lrk lrv lrl lrr) r))
          (SBin (ls + SMapSize r + 1) lrk lrv
            (SBin (SMapSize ll + SMapSize lrl + 1) lk lv ll lrl)
            (SBin (SMapSize lrr + SMapSize r + 1) k v lrr r)))
        (SBin (ls + SMapSize r + 1) k v (SBin ls lk lv ll (SBin lrs lrk lrv lrl lrr)) r)

type family SMapBalanceR (k :: Symbol) (v :: a) (l :: SMap a) (r :: SMap a) :: SMap a where
  SMapBalanceR k v STip STip
    = SBin 1 k v STip STip

  SMapBalanceR k v STip (SBin 1 rk rv STip STip)
    = SBin 2 k v STip (SBin 1 rk rv STip STip)

  SMapBalanceR k v STip (SBin 2 rk rv STip rr)
    = SBin 3 rk rv (SBin 1 k v STip STip) rr

  SMapBalanceR k v STip (SBin 2 rk rv (SBin 1 rlk rlv STip STip) STip)
    = SBin 3 rlk rlv (SBin 1 k v STip STip) (SBin 1 rk rv STip STip)

  SMapBalanceR k v STip (SBin rs rk rv (SBin rls rlk rlv rll rlr) rr)
    = If (CmpNat rls (2 * SMapSize rr) == LT)
        (SBin (rs + 1) rk rv (SBin (rls + 1) k v STip (SBin rls rlk rlv rll rlr)) rr)
        (SBin (rs + 1) rlk rlv
          (SBin (SMapSize rll + 1) k v STip rll)
          (SBin (SMapSize rlr + SMapSize rr + 1) rk rv rlr rr))

  SMapBalanceR k v l STip
    = SBin (SMapSize l + 1) k v l STip

  SMapBalanceR k v l (SBin rs rk rv (SBin rls rlk rlv rll rlr) rr)
    = If (CmpNat rs (2 * SMapSize l) == GT)
        (If (CmpNat rls (2 * SMapSize rr) == LT)
          (SBin (SMapSize l + rs + 1) rk rv (SBin (SMapSize l + rls + 1) k v l (SBin rls rlk rlv rll rlr)) rr)
          (SBin (SMapSize l + rs + 1) rlk rlv
            (SBin (SMapSize l + SMapSize rll + 1) k v l rll)
            (SBin (SMapSize rlr + SMapSize rr + 1) rk rv rlr rr)))
        (SBin (SMapSize l + rs + 1) k v l (SBin rs rk rv (SBin rls rlk rlv rll rlr) rr))

type family SMapGlue (l :: SMap a) (r :: SMap a) :: SMap a where
  SMapGlue STip                  STip                  = STip
  SMapGlue STip                  r                     = r
  SMapGlue l                     STip                  = l
  SMapGlue (SBin ls lk lv ll lr) (SBin rs rk rv rl rr) = If (CmpNat ls rs == GT)
    (SMapGlueR (SMapMaxViewSure lk lv ll lr) (SBin rs rk rv rl rr))
    (SMapGlueL (SBin ls lk lv ll lr) (SMapMinViewSure rk rv rl rr))

data SMapView a = SMapView Symbol a (SMap a)

type family SMapGlueR (l :: SMapView a) (r :: SMap a) :: SMap a where
  SMapGlueR ('SMapView k v l) r = SMapBalanceR k v l r

type family SMapGlueL (l :: SMap a) (r :: SMapView a) :: SMap a where
  SMapGlueL l ('SMapView k v r) = SMapBalanceL k v l r

type family SMapMaxViewSure (k :: Symbol) (v :: a) (l :: SMap a) (r :: SMap a) :: SMapView a where
  SMapMaxViewSure k v l STip                  = 'SMapView k v l
  SMapMaxViewSure k v l (SBin _s rk rv rl rr) = SMapMaxViewSure_ k v l (SMapMaxViewSure rk rv rl rr)

type family SMapMaxViewSure_ (k :: Symbol) (v :: a) (l :: SMap a) (view :: SMapView a) :: SMapView a where
  SMapMaxViewSure_ k v l ('SMapView km vm r) = 'SMapView km vm (SMapBalanceL k v l r)

type family SMapMinViewSure (k :: Symbol) (v :: a) (l :: SMap a) (r :: SMap a) :: SMapView a where
  SMapMinViewSure k v STip                  r = 'SMapView k v r
  SMapMinViewSure k v (SBin _s lk lv ll lr) r = SMapMinViewSure_ k v (SMapMinViewSure lk lv ll lr) r

type family SMapMinViewSure_ (k :: Symbol) (v :: a) (view :: SMapView a) (r :: SMap a) :: SMapView a where
  SMapMinViewSure_ k v ('SMapView km vm l) r = 'SMapView km vm (SMapBalanceL k v l r)

type family If (b :: Bool) (x :: k) (y :: k) :: k where
  If True  x y = x
  If False x y = y

type family a == b :: Bool where
  a == a = True
  a == b = False

type family (x :: Bool) && (y :: Bool) :: Bool where
  True && True = True
  x    && y    = False

type family (x :: Bool) || (y :: Bool) :: Bool where
  False || False = False
  x     || y     = True

type family Not (x :: Bool) :: Bool where
  Not True  = False
  Not False = True

type family CaseCmp (o :: Ordering) (lt :: k) (eq :: k) (gt :: k) :: k where
  CaseCmp LT lt eq gt = lt
  CaseCmp EQ lt eq gt = eq
  CaseCmp GT lt eq gt = gt

type family CaseCmpNE (o :: Ordering) (lt :: k) (gt :: k) :: k where
  CaseCmpNE LT lt gt = lt
  CaseCmpNE GT lt gt = gt

type family (xs :: [k]) ++ (ys :: [k]) :: [k] where
  '[] ++ ys    = ys
  (x:xs) ++ ys = x : (xs ++ ys)
{-
data SSet (n :: Nat) v l r

type SSetEmpty = SSet 0 Void Void Void
type SSetSing a = SSet 1 a Void Void

type family SSetInsert (a :: Symbol) (s :: SSet n v l r) where
  SSetInsert a (SSet 0 Void Void Void) = SSet 1 a Void Void
  SSetInsert a (SSet n v    l    r   ) = SSet n v l    r

newtype HSet (as :: [Type]) = HSet { getHSet :: HashMap SomeTypeRep Any }

data Any where
  Any :: ∀ a. a -> Any

type family (a :: k) ! (as :: [k]) :: Bool where
  a ! '[]      = False
  a ! (a : _ ) = True
  a ! (_ : as) = a ! as

empty :: HSet '[]
empty = HSet Map.empty

singleton :: ∀ a. Typeable a => a -> HSet '[a]
singleton a = HSet $ Map.singleton (someTypeRep (Proxy @a)) (Any a)

insert :: ∀ a as. (Typeable a, a ! as ~ False) => a -> HSet as -> HSet (a : as)
insert a m = HSet $ Map.insert (someTypeRep (Proxy @a)) (Any a) (coerce m)

update :: ∀ a as. (Typeable a, a ! as ~ True) => a -> HSet as -> HSet as
update a m = HSet $ Map.insert (someTypeRep (Proxy @a)) (Any a) (coerce m)

lookup :: ∀ a as. (Typeable a, a ! as ~ True) => ∀ proxy. proxy a -> HSet as -> a
lookup p m = fromMaybe (error msg) (want p m)
  where msg = "Data.HSet: lookup failed. This should be impossible."

want :: ∀ proxy a as. Typeable a => proxy a -> HSet as -> Maybe a
want p (HSet m) = case Map.lookup (someTypeRep p) m of
  Just (Any a) -> Just $ unsafeCoerce a
  Nothing      -> Nothing

class HSize (a :: [Type]) where
  null :: HSet a -> Bool
  size :: HSet a -> Int

instance HSize '[] where
  null _ = True
  size _ = 0

instance {-# OVERLAPPABLE #-} HSize as => HSize (a : as) where
  null _ = False
  size _ = 1 + size (undefined :: HSet as)

class DemoteBool (b :: Bool) where demoteBool :: ∀ proxy. proxy b -> Bool
instance DemoteBool False where demoteBool _ = False
instance DemoteBool True  where demoteBool _ = True

member :: ∀ proxy a as b. (b ~ a ! as, DemoteBool b) => proxy a -> HSet as -> Bool
member _ _ = demoteBool (Proxy @b)

type family Union (as :: [k]) (bs :: [k]) :: [k] where
  Union as '[]      = as
  Union as (b : bs) = Union' (b ! as) as (b : bs)

type family Union' (b :: Bool) (as :: [k]) (bs :: [k]) :: [k] where
  Union' b     as '[]      = as
  Union' False as (b : bs) = b : Union as bs
  Union' True  as (b : bs) = Union as bs

union :: ∀ as bs. HSet as -> HSet bs -> HSet (Union as bs)
union (HSet l) (HSet r) = HSet $ Map.union l r

type family (x :: Bool) ^&& (y :: Bool) :: Bool where
  True ^&& True = True
  x    ^&& y    = False

type family (x :: Bool) ^|| (y :: Bool) :: Bool where
  False ^|| False = False
  x     ^|| y     = True

type family (as :: [k]) =~= (bs :: [k]) :: Bool where
  '[]      =~= '[]      = True
  '[]      =~= bs       = False
  as       =~= '[]      = False
  (a : as) =~= (a : bs) = as =~= bs
  (a : as) =~= (b : bs) = (a ! bs) ^&& (b ! as) ^&& (Delete a bs =~= Delete b as)

type family Delete (a :: k) (as :: [k]) where
  Delete a '[]      = '[]
  Delete a (a : bs) = bs
  Delete a (b : bs) = b : Delete a bs

type family Difference (as :: [k]) (bs :: [k]) :: [k] where
  Difference '[]      bs  = '[]
  Difference as       '[] = as
  Difference (a : as) bs  = If (a ! bs) (Difference as (Delete a bs)) (a : Difference as bs)

type family Subset (as :: [k]) (bs :: [k]) :: Bool where
  Subset '[]      bs       = True
  Subset (a : as) '[]      = False
  Subset as       (a : as) = True
  Subset (a : as) (a : bs) = Subset as bs
  Subset (a : as) (b : bs) = (a ! bs) ^&& Subset as (b : Delete a bs)

delete :: ∀ proxy a as. Typeable a => proxy a -> HSet as -> HSet (Delete a as)
delete _ m = HSet $ Map.delete (someTypeRep (Proxy @a)) (coerce m)

isSubsetOf :: ∀ s1 s2 as bs b. (b ~ Subset as bs, DemoteBool b) => s1 as -> s2 bs -> Bool
isSubsetOf _ _ = demoteBool (Proxy @(Subset as bs))

class Trivial a
instance Trivial a

difference :: ∀ proxy as bs. HFoldr Trivial bs => HSet as -> proxy bs -> HSet (Difference as bs)
difference (HSet m) _ = HSet $ Map.difference m (hmap @Trivial (const ()) (HSet Map.empty :: HSet bs))

type family Intersection (as :: [k]) (bs :: [k]) :: [k] where
  Intersection '[]      bs       = '[]
  Intersection as       '[]      = '[]
  Intersection (a : as) (a : bs) = a : Intersection as bs
  Intersection (a : as) bs       = If (a ! bs) (a : Intersection as (Delete a bs)) (Intersection as bs)

intersection :: ∀ as bs. HSet as -> HSet bs -> HSet (Intersection as bs)
intersection (HSet a) (HSet b) = HSet $ Map.intersection a b

censor :: Subset bs as ~ True => HSet as -> HSet bs
censor = coerce

class HFoldr (cls :: Type -> Constraint) (as :: [Type]) where
  hfoldr :: (∀ a. (Typeable a, cls a) => a -> b -> b) -> b -> HSet as -> b

instance HFoldr cls '[] where
  hfoldr _ z _ = z

instance (Typeable a, cls a, HFoldr cls as) => HFoldr cls (a : as) where
  hfoldr f z s = f (lookup (Proxy @a) s) (hfoldr @cls f z (censor s :: HSet as))

hmap :: ∀ cls as b. HFoldr cls as => (∀ a. cls a => a -> b) -> HSet as -> HashMap SomeTypeRep b
hmap f = hfoldr @cls (\val -> Map.insert (someTypeRep (Identity val)) (f val)) Map.empty

instance HFoldr Show as => Show (HSet as) where
  showsPrec _ s = showListWith showPair (Map.toList (hmap @Show shows s))
    where showPair (ty, str) = showParen True (shows ty . showChar ',' . str)

class (Typeable a, cls a, a ! as ~ True) => H cls as a
instance (Typeable a, cls a, a ! as ~ True) => H cls as a

instance HFoldr (H Eq as) as => Eq (HSet as) where
  xs == ys = hfoldr @(H Eq as) (\y acc -> acc && y == lookup (Identity y) xs) True ys

instance (HFoldr (H Eq as) as, HFoldr (H Ord as) as) => Ord (HSet as) where
  xs `compare` ys = hfoldr @(H Ord as) (\x acc -> x `compare` lookup (Identity x) ys <> acc) EQ xs

instance Semigroup (HSet as) where
  HSet l <> HSet r = HSet $ Map.union l r

instance Monoid (HSet '[]) where
  mempty = empty

instance (HFoldr (H Eq as) as, HFoldr (H Hashable as) as) => Hashable (HSet as) where
  hashWithSalt = hfoldr @(H Hashable as) (flip hashWithSalt)
-}
