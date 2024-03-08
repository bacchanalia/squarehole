module Data.Type.Function where

import GHC.TypeLits

type family App1 (f :: ix) (x :: a) :: b
type family App2 (f :: ix) (x :: a) (y :: b) :: c
type family App3 (f :: ix) (x :: a) (y :: b) (z :: c) :: d

data Id
type instance App1 Id x = x

data ConstK a = Const a
type instance App1 (Const k) x = k
type instance App2 (Const k) x y = k
type instance App3 (Const k) x y z = k

data ErrorK = Error ErrorMessage
type instance App1 (Error msg) x = TypeError msg
type instance App2 (Error msg) x y = TypeError msg
type instance App3 (Error msg) x y z = TypeError msg

data AppIxsK a = AppIxs [Nat] a

type Proj (n :: Nat) = AppIxs '[n] Id

type instance App1 (AppIxs '[1] f) x = App1 f x

type instance App1 (AppIxs '[1,1] f) x = App2 f x x

type instance App1 (AppIxs '[1,1,1] f) x = App3 f x x x

type instance App2 (AppIxs '[1] f) x y = App1 f x
type instance App2 (AppIxs '[2] f) x y = App1 f y

type instance App2 (AppIxs '[1,1] f) x y = App2 f x x
type instance App2 (AppIxs '[1,2] f) x y = App2 f x y
type instance App2 (AppIxs '[2,1] f) x y = App2 f y y
type instance App2 (AppIxs '[2,2] f) x y = App2 f y y

type instance App2 (AppIxs '[1,1,1] f) x y = App3 f x x x
type instance App2 (AppIxs '[1,1,2] f) x y = App3 f x x y
type instance App2 (AppIxs '[1,2,1] f) x y = App3 f x y x
type instance App2 (AppIxs '[1,2,2] f) x y = App3 f x y y
type instance App2 (AppIxs '[2,1,1] f) x y = App3 f y x x
type instance App2 (AppIxs '[2,1,2] f) x y = App3 f y x y
type instance App2 (AppIxs '[2,2,1] f) x y = App3 f y y x
type instance App2 (AppIxs '[2,2,2] f) x y = App3 f y y y

type instance App3 (AppIxs '[1] f) x y z = App1 f x
type instance App3 (AppIxs '[2] f) x y z = App1 f y
type instance App3 (AppIxs '[3] f) x y z = App1 f z

type instance App3 (AppIxs '[1,1] f) x y z = App2 f x x
type instance App3 (AppIxs '[1,2] f) x y z = App2 f x y
type instance App3 (AppIxs '[1,3] f) x y z = App2 f x z
type instance App3 (AppIxs '[2,1] f) x y z = App2 f y x
type instance App3 (AppIxs '[2,2] f) x y z = App2 f y y
type instance App3 (AppIxs '[2,3] f) x y z = App2 f y z
type instance App3 (AppIxs '[3,1] f) x y z = App2 f z x
type instance App3 (AppIxs '[3,2] f) x y z = App2 f z y
type instance App3 (AppIxs '[3,3] f) x y z = App2 f z z

type instance App3 (AppIxs '[1,1,1] f) x y z = App3 f x x x
type instance App3 (AppIxs '[1,1,2] f) x y z = App3 f x x y
type instance App3 (AppIxs '[1,1,3] f) x y z = App3 f x x z
type instance App3 (AppIxs '[1,2,1] f) x y z = App3 f x y x
type instance App3 (AppIxs '[1,2,2] f) x y z = App3 f x y y
type instance App3 (AppIxs '[1,2,3] f) x y z = App3 f x y z
type instance App3 (AppIxs '[1,3,1] f) x y z = App3 f x z x
type instance App3 (AppIxs '[1,3,2] f) x y z = App3 f x z y
type instance App3 (AppIxs '[1,3,3] f) x y z = App3 f x z z
type instance App3 (AppIxs '[2,1,1] f) x y z = App3 f y x x
type instance App3 (AppIxs '[2,1,2] f) x y z = App3 f y x y
type instance App3 (AppIxs '[2,1,3] f) x y z = App3 f y x z
type instance App3 (AppIxs '[2,2,1] f) x y z = App3 f y y x
type instance App3 (AppIxs '[2,2,2] f) x y z = App3 f y y y
type instance App3 (AppIxs '[2,2,3] f) x y z = App3 f y y z
type instance App3 (AppIxs '[2,3,1] f) x y z = App3 f y z x
type instance App3 (AppIxs '[2,3,2] f) x y z = App3 f y z y
type instance App3 (AppIxs '[2,3,3] f) x y z = App3 f y z z
type instance App3 (AppIxs '[3,1,1] f) x y z = App3 f z x x
type instance App3 (AppIxs '[3,1,2] f) x y z = App3 f z x y
type instance App3 (AppIxs '[3,1,3] f) x y z = App3 f z x z
type instance App3 (AppIxs '[3,2,1] f) x y z = App3 f z y x
type instance App3 (AppIxs '[3,2,2] f) x y z = App3 f z y y
type instance App3 (AppIxs '[3,2,3] f) x y z = App3 f z y z
type instance App3 (AppIxs '[3,3,1] f) x y z = App3 f z z x
type instance App3 (AppIxs '[3,3,2] f) x y z = App3 f z z y
type instance App3 (AppIxs '[3,3,3] f) x y z = App3 f z z z

type family Uncurry (f :: a_b_c) (p :: (a, b)) :: c where
  Uncurry f '(x, y) = App2 f x y

type family Uncurry3 (f :: a_b_c_d) (p :: (a, b, c)) :: d where
  Uncurry3 f '(x, y, z) = App3 f x y z

type family CaseMaybe (x :: Maybe a) (n :: b) (f :: a_b) :: b where
  CaseMaybe Nothing  n f = n
  CaseMaybe (Just x) n f = App1 f x

type family CaseList (x :: [a]) (z :: b) (f :: a_as_b) :: b where
  CaseList '[]    z f = z
  CaseList (x:xs) z f = App2 f x xs

type family CaseEither (x :: Either a b) (l :: a_c) (r :: b_c) :: c where
  CaseEither (Left  x) l r = App1 l x
  CaseEither (Right x) l r = App1 r x
