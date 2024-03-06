module Data.HSet where

import Prelude hiding (lookup, map, null)
import Data.Constraint
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as Map
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy(..))
import GHC.Prim (coerce)
import Type.Reflection (SomeTypeRep, Typeable, someTypeRep)
import Unsafe.Coerce (unsafeCoerce)
import Text.Show

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

unionTLVL :: ∀ as bs. HSet as -> HSet bs -> HSet (Union as bs)
unionTLVL (HSet l) (HSet r) = HSet $ Map.union l r

unionTLVR :: ∀ as bs. HSet as -> HSet bs -> HSet (Union as bs)
unionTLVR (HSet l) (HSet r) = HSet $ Map.union r l

unionTRVL :: ∀ as bs. HSet as -> HSet bs -> HSet (Union bs as)
unionTRVL (HSet l) (HSet r) = HSet $ Map.union l r

unionTRVR :: ∀ as bs. HSet as -> HSet bs -> HSet (Union bs as)
unionTRVR (HSet l) (HSet r) = HSet $ Map.union r l

type family (x :: Bool) ^&& (y :: Bool) :: Bool where
  True ^&& True = True
  x    ^&& y    = False

type family (x :: Bool) ^|| (y :: Bool) :: Bool where
  False ^|| False = False
  x     ^|| y     = True

type family If (b :: Bool) (x :: k) (y :: k) :: k where
  If True  x y = x
  If False x y = y

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
  Subset (a : as) (a : bs) = Subset as bs
  Subset (a : as) (b : bs) = (a ! bs) ^&& Subset as (b : Delete a bs)

delete :: ∀ proxy a as. Typeable a => proxy a -> HSet as -> HSet (Delete a as)
delete _ m = HSet $ Map.delete (someTypeRep (Proxy @a)) (coerce m)

isSubsetOf :: ∀ s1 s2 as bs b. (b ~ Subset as bs, DemoteBool b) => s1 as -> s2 bs -> Bool
isSubsetOf _ _ = demoteBool (Proxy @(Subset as bs))

--difference :: ∀ as bs. HSet as -> HSet bs -> HSet (Difference as bs)
--difference (HSet a) (HSet b) = HSet $ Map.difference a b

class (Typeable a, DemoteBool (a ! bs)) => Fsh bs a
instance (Typeable a, DemoteBool (a ! bs)) => Fsh bs a

difference :: ∀ proxy as bs. HSet as -> proxy bs -> HSet (Difference as bs)
difference s p = HSet $ hfoldr @(Fsh bs) f Map.empty s
  where
    f :: ∀a. Fsh bs a => SomeTypeRep -> a -> HashMap SomeTypeRep Any -> HashMap SomeTypeRep Any
    f ty val acc = if demoteBool (Proxy @(a ! bs)) then acc else Map.insert ty (Any val) acc

type family Intersection (as :: [k]) (bs :: [k]) :: [k] where
  Intersection '[]      bs       = '[]
  Intersection as       '[]      = '[]
  Intersection (a : as) (a : bs) = a : Intersection as bs
  Intersection (a : as) bs       = If (a ! bs) (a : Intersection as (Delete a bs)) (Intersection as bs)

intersectionTLVL :: ∀ as bs. HSet as -> HSet bs -> HSet (Intersection as bs)
intersectionTLVL (HSet a) (HSet b) = HSet $ Map.intersection a b

intersectionTLVR :: ∀ as bs. HSet as -> HSet bs -> HSet (Intersection as bs)
intersectionTLVR (HSet a) (HSet b) = HSet $ Map.intersection b a

intersectionTRVL :: ∀ as bs. HSet as -> HSet bs -> HSet (Intersection bs as)
intersectionTRVL (HSet a) (HSet b) = HSet $ Map.intersection a b

intersectionTRVR :: ∀ as bs. HSet as -> HSet bs -> HSet (Intersection bs as)
intersectionTRVR (HSet a) (HSet b) = HSet $ Map.intersection b a

censor :: Subset bs as ~ True => HSet as -> HSet bs
censor = coerce

class HFoldr (cls :: Type -> Constraint) (as :: [Type]) where
  hfoldr :: (∀ a. cls a => SomeTypeRep -> a -> b -> b) -> b -> HSet as -> b

instance HFoldr cls '[] where
  hfoldr _ z _ = z

instance (Typeable a, cls a, HFoldr cls as) => HFoldr cls (a : as) where
  hfoldr f z s = f (someTypeRep p) (lookup p s) (hfoldr @cls f z (delete p s :: HSet as))
    where p = Proxy @a

map :: ∀ cls as b. HFoldr cls as => (∀ a. cls a => a -> b) -> HSet as -> HashMap SomeTypeRep b
map f = hfoldr @cls (\ty val -> Map.insert ty (f val)) Map.empty

instance HFoldr Show as => Show (HSet as) where
  showsPrec _ s = showListWith showPair (Map.toList (map @Show shows s))
    where showPair (ty, str) = showParen True (shows ty . showChar ',' . str)
