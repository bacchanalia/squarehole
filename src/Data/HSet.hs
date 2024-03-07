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

data SMap = STip | SBin Nat Symbol Type SMap SMap

type family SMapSize (m :: SMap) :: Nat where
  SMapSize STip                 = 0
  SMapSize (SBin s _k _v _l _r) = s

type family SMapMember (k :: Symbol) (m :: SMap) :: Bool where
  SMapMember k STip                = False
  SMapMember k (SBin _s mk _v l r) = CaseCmp (CmpSymbol k mk)
    {- LT -} (SMapMember k l)
    {- EQ -} True
    {- GT -} (SMapMember k r)

type family SMapLookup (k :: Symbol) (m :: SMap) :: Maybe Type where
  SMapLookup _k STip               = Nothing
  SMapLookup k  (SBin _s mk v l r) = CaseCmp (CmpSymbol k mk)
    {- LT -} (SMapLookup k l)
    {- EQ -} (Just v)
    {- GT -} (SMapLookup k r)

type family SMapInsert (k :: Symbol) (v :: Type) (m :: SMap) :: SMap where
  SMapInsert k v STip               = SBin 1 k v STip STip
  SMapInsert k v (SBin  s  k _v l r) = SBin s k v l r
  SMapInsert k v (SBin _s mk mv l r) = If (CmpSymbol k mk == LT)
      (SMapBalanceL mk mv (SMapInsert k v l) r)
      (SMapBalanceR mk mv l (SMapInsert k v r))

type family SMapBalanceL (k :: Symbol) (v :: Type) (l :: SMap) (r :: SMap) :: SMap where
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

type family SMapBalanceR (k :: Symbol) (v :: Type) (l :: SMap) (r :: SMap) :: SMap where
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

{-
type family SSetInsert (a :: Symbol) (s :: SSet Symbol) :: SSet Symbol where
  SSetInsert a STip           = SBin 1 a STip STip
  SSetInsert a (SBin n v l r) = If (SElem a (SBin n v l r)) (SBin n v l r)
    (SSetBalance
      (If (CmpSymbol a v == LT)
        (SBin (n+1) (SSetInsert' a l) r)
        (SBin (n+1) l (SSetInsert' a r))))

type family SSetInsert' (a :: Symbol) (s :: SSet Symbol) :: SSet Symbol where
  SSetInsert' a (SBin n v l r) = 

type family SSetBalance (s :: SSet Symbol) :: SSet Symbol where
  SSetBalance s = s

type family SSetSize (s :: SSet k) :: Nat where
  SSetSize STip           = 0
  SSetSize (SBin n v l r) = n

type family SElem (a :: Symbol) (s :: SSet Symbol) :: Bool where
  SElem a STip           = False
  SElem a (SBin n a l r) = True
  SElem a (SBin n v l r) = If (CmpSymbol a v == LT) (SElem a l) (SElem a r)
-}

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
