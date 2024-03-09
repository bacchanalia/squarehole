module Data.Type.Function where

import Data.Kind
import Data.Type.Bool
import Data.Type.Equality
import Data.Type.Ord
import GHC.TypeError
import GHC.TypeLits

type family App1 (f :: ix) (x1 :: a1) :: b
type family App2 (f :: ix) (x1 :: a1) (x2 :: a2) :: b
type family App3 (f :: ix) (x1 :: a1) (x2 :: a2) (x3 :: a3) :: b
type family App4 (f :: ix) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) :: b
type family App5 (f :: ix) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5) :: b
type family App6 (f :: ix) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5) (x6 :: a6) :: b
type family App7 (f :: ix) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5) (x6 :: a6) (x7 :: a7) :: b

data Id
type instance App1 Id x1 = x1

-- This could almost be:
-- type Error (msg :: ErrorMessage) = Const (TypeError msg)
-- but TypeError is weird.
data ErrorK = Error ErrorMessage
type instance App1 (Error msg) x1 = TypeError msg
type instance App2 (Error msg) x1 x2 = TypeError msg
type instance App3 (Error msg) x1 x2 x3 = TypeError msg
type instance App4 (Error msg) x1 x2 x3 x4 = TypeError msg
type instance App5 (Error msg) x1 x2 x3 x4 x5 = TypeError msg
type instance App6 (Error msg) x1 x2 x3 x4 x5 x6 = TypeError msg
type instance App7 (Error msg) x1 x2 x3 x4 x5 x6 x7 = TypeError msg

infixl 0 type ($)
type (x :: a) $ (xs :: b) = HCons x xs


--type Const (x :: a) = Id $ AThen ADrop $ x $ HNil
type Const (x :: a) = HCons Id (HCons (AThen ADrop) (HCons (AApp x) HNil))
type Proj (n :: Nat) = HCons Id (HCons (ARep (n - 1) ADrop) (HCons AUse HNil))
type ArgTail (fun :: f) = HCons fun (HCons ADrop (HCons (AThen AUse) HNil))

data T1
data T2
type instance App2 T1 x y = x
type instance App2 T2 x y = y

data AUse
data ADrop
data AApp a
data ARepK a = ARep Nat a
data AThen a

data HCons a as
data HNil

type family Apply (fun :: f) (acc :: as) :: b

type family ArgAcc0 (fun :: f) (args :: argdesc) (acc :: as) :: b where
  ArgAcc0 f HNil                      acc = Apply f acc

  ArgAcc0 f (HCons (ADrop     ) args) acc = ArgAcc0 f args acc
  ArgAcc0 f (HCons (AUse      ) args) acc = ArgAcc0 f args acc
  ArgAcc0 f (HCons (AApp a    ) args) acc = ArgAcc0 f args (HCons a  acc)

  ArgAcc0 f (HCons (ARep 0 arg) args) acc = ArgAcc0 f args                                        acc
  ArgAcc0 f (HCons (ARep 1 arg) args) acc = ArgAcc0 f (HCons arg args)                            acc
  ArgAcc0 f (HCons (ARep n arg) args) acc = ArgAcc0 f (HCons arg (HCons (ARep (n - 1) arg) args)) acc
  ArgAcc0 f (HCons (AThen  arg) args) acc = ArgAcc0 f args                                        acc

type instance App1 (HCons f args) x1 = ArgAcc1 f args HNil x1
type instance Apply f (HCons a1 HNil) = App1 f a1
type family ArgAcc1 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) :: b where
  ArgAcc1 f HNil                      acc x1 = Apply f acc

  ArgAcc1 f (HCons (ADrop     ) args) acc x1 = ArgAcc0 f args acc
  ArgAcc1 f (HCons (AUse      ) args) acc x1 = ArgAcc0 f args (HCons x1 acc)
  ArgAcc1 f (HCons (AApp a    ) args) acc x1 = ArgAcc1 f args (HCons a  acc) x1

  ArgAcc1 f (HCons (ARep 0 arg) args) acc x1 = ArgAcc1 f args                                        acc x1
  ArgAcc1 f (HCons (ARep 1 arg) args) acc x1 = ArgAcc1 f (HCons arg args)                            acc x1
  ArgAcc1 f (HCons (ARep n arg) args) acc x1 = ArgAcc1 f (HCons arg (HCons (ARep (n - 1) arg) args)) acc x1
  ArgAcc1 f (HCons (AThen  arg) args) acc x1 = ArgAcc1 f (HCons arg (HCons (AThen arg) args))        acc x1

type instance App2 (HCons f args) x1 x2 = ArgAcc2 f args HNil x1 x2
type instance Apply f (HCons a2 (HCons a1 HNil)) = App2 f a1 a2
type family ArgAcc2 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) :: b where
  ArgAcc2 f HNil                      acc x1 x2 = Apply f acc

  ArgAcc2 f (HCons (ADrop     ) args) acc x1 x2 = ArgAcc1 f args acc            x2
  ArgAcc2 f (HCons (AUse      ) args) acc x1 x2 = ArgAcc1 f args (HCons x1 acc) x2
  ArgAcc2 f (HCons (AApp a    ) args) acc x1 x2 = ArgAcc2 f args (HCons a  acc) x1 x2

  ArgAcc2 f (HCons (ARep 0 arg) args) acc x1 x2 = ArgAcc2 f args                                        acc x1 x2
  ArgAcc2 f (HCons (ARep 1 arg) args) acc x1 x2 = ArgAcc2 f (HCons arg args)                            acc x1 x2
  ArgAcc2 f (HCons (ARep n arg) args) acc x1 x2 = ArgAcc2 f (HCons arg (HCons (ARep (n - 1) arg) args)) acc x1 x2
  ArgAcc2 f (HCons (AThen  arg) args) acc x1 x2 = ArgAcc2 f (HCons arg (HCons (AThen arg) args))        acc x1 x2

type instance App3 (HCons f args) x1 x2 x3 = ArgAcc3 f args HNil x1 x2 x3
type instance Apply f (HCons a3 (HCons a2 (HCons a1 HNil))) = App3 f a1 a2 a3
type family ArgAcc3 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) :: b where
  ArgAcc3 f HNil                      acc x1 x2 x3 = Apply f acc

  ArgAcc3 f (HCons (ADrop     ) args) acc x1 x2 x3 = ArgAcc2 f args acc            x2 x3
  ArgAcc3 f (HCons (AUse      ) args) acc x1 x2 x3 = ArgAcc2 f args (HCons x1 acc) x2 x3
  ArgAcc3 f (HCons (AApp a    ) args) acc x1 x2 x3 = ArgAcc3 f args (HCons a  acc) x1 x2 x3

  ArgAcc3 f (HCons (ARep 0 arg) args) acc x1 x2 x3 = ArgAcc3 f args                                        acc x1 x2 x3
  ArgAcc3 f (HCons (ARep 1 arg) args) acc x1 x2 x3 = ArgAcc3 f (HCons arg args)                            acc x1 x2 x3
  ArgAcc3 f (HCons (ARep n arg) args) acc x1 x2 x3 = ArgAcc3 f (HCons arg (HCons (ARep (n - 1) arg) args)) acc x1 x2 x3
  ArgAcc3 f (HCons (AThen  arg) args) acc x1 x2 x3 = ArgAcc3 f (HCons arg (HCons (AThen arg) args))        acc x1 x2 x3

type instance App4 (HCons f args) x1 x2 x3 x4 = ArgAcc4 f args HNil x1 x2 x3 x4
type instance Apply f (HCons a4 (HCons a3 (HCons a2 (HCons a1 HNil)))) = App4 f a1 a2 a3 a4
type family ArgAcc4 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) :: b where
  ArgAcc4 f HNil                      acc x1 x2 x3 x4 = Apply f acc

  ArgAcc4 f (HCons (ADrop     ) args) acc x1 x2 x3 x4 = ArgAcc3 f args acc            x2 x3 x4
  ArgAcc4 f (HCons (AUse      ) args) acc x1 x2 x3 x4 = ArgAcc3 f args (HCons x1 acc) x2 x3 x4
  ArgAcc4 f (HCons (AApp a    ) args) acc x1 x2 x3 x4 = ArgAcc4 f args (HCons a  acc) x1 x2 x3 x4

  ArgAcc4 f (HCons (ARep 0 arg) args) acc x1 x2 x3 x4 = ArgAcc4 f args                                        acc x1 x2 x3 x4
  ArgAcc4 f (HCons (ARep 1 arg) args) acc x1 x2 x3 x4 = ArgAcc4 f (HCons arg args)                            acc x1 x2 x3 x4
  ArgAcc4 f (HCons (ARep n arg) args) acc x1 x2 x3 x4 = ArgAcc4 f (HCons arg (HCons (ARep (n - 1) arg) args)) acc x1 x2 x3 x4
  ArgAcc4 f (HCons (AThen  arg) args) acc x1 x2 x3 x4 = ArgAcc4 f (HCons arg (HCons (AThen arg) args))        acc x1 x2 x3 x4

type instance App5 (HCons f args) x1 x2 x3 x4 x5 = ArgAcc5 f args HNil x1 x2 x3 x4 x5
type instance Apply f (HCons a5 (HCons a4 (HCons a3 (HCons a2 (HCons a1 HNil))))) = App5 f a1 a2 a3 a4 a5
type family ArgAcc5 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5) :: b where
  ArgAcc5 f HNil                      acc x1 x2 x3 x4 x5 = Apply f acc

  ArgAcc5 f (HCons (ADrop     ) args) acc x1 x2 x3 x4 x5 = ArgAcc4 f args acc            x2 x3 x4 x5
  ArgAcc5 f (HCons (AUse      ) args) acc x1 x2 x3 x4 x5 = ArgAcc4 f args (HCons x1 acc) x2 x3 x4 x5
  ArgAcc5 f (HCons (AApp a    ) args) acc x1 x2 x3 x4 x5 = ArgAcc5 f args (HCons a  acc) x1 x2 x3 x4 x5

  ArgAcc5 f (HCons (ARep 0 arg) args) acc x1 x2 x3 x4 x5 = ArgAcc5 f args                                        acc x1 x2 x3 x4 x5
  ArgAcc5 f (HCons (ARep 1 arg) args) acc x1 x2 x3 x4 x5 = ArgAcc5 f (HCons arg args)                            acc x1 x2 x3 x4 x5
  ArgAcc5 f (HCons (ARep n arg) args) acc x1 x2 x3 x4 x5 = ArgAcc5 f (HCons arg (HCons (ARep (n - 1) arg) args)) acc x1 x2 x3 x4 x5
  ArgAcc5 f (HCons (AThen  arg) args) acc x1 x2 x3 x4 x5 = ArgAcc5 f (HCons arg (HCons (AThen arg) args))        acc x1 x2 x3 x4 x5

type instance App6 (HCons f args) x1 x2 x3 x4 x5 x6 = ArgAcc6 f args HNil x1 x2 x3 x4 x5 x6
type instance Apply f (HCons a6 (HCons a5 (HCons a4 (HCons a3 (HCons a2 (HCons a1 HNil)))))) = App6 f a1 a2 a3 a4 a5 a6
type family ArgAcc6 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5) (x6 :: a6) :: b where
  ArgAcc6 f HNil                      acc x1 x2 x3 x4 x5 x6 = Apply f acc

  ArgAcc6 f (HCons (ADrop     ) args) acc x1 x2 x3 x4 x5 x6 = ArgAcc5 f args acc            x2 x3 x4 x5 x6
  ArgAcc6 f (HCons (AUse      ) args) acc x1 x2 x3 x4 x5 x6 = ArgAcc5 f args (HCons x1 acc) x2 x3 x4 x5 x6
  ArgAcc6 f (HCons (AApp a    ) args) acc x1 x2 x3 x4 x5 x6 = ArgAcc6 f args (HCons a  acc) x1 x2 x3 x4 x5 x6

  ArgAcc6 f (HCons (ARep 0 arg) args) acc x1 x2 x3 x4 x5 x6 = ArgAcc6 f args                                        acc x1 x2 x3 x4 x5 x6
  ArgAcc6 f (HCons (ARep 1 arg) args) acc x1 x2 x3 x4 x5 x6 = ArgAcc6 f (HCons arg args)                            acc x1 x2 x3 x4 x5 x6
  ArgAcc6 f (HCons (ARep n arg) args) acc x1 x2 x3 x4 x5 x6 = ArgAcc6 f (HCons arg (HCons (ARep (n - 1) arg) args)) acc x1 x2 x3 x4 x5 x6
  ArgAcc6 f (HCons (AThen  arg) args) acc x1 x2 x3 x4 x5 x6 = ArgAcc6 f (HCons arg (HCons (AThen arg) args))        acc x1 x2 x3 x4 x5 x6

type instance App7 (HCons f args) x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f args HNil x1 x2 x3 x4 x5 x6 x7
type instance Apply f (HCons a7 (HCons a6 (HCons a5 (HCons a4 (HCons a3 (HCons a2 (HCons a1 HNil))))))) = App7 f a1 a2 a3 a4 a5 a6 a7
type family ArgAcc7 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5) (x6 :: a6) (x7 :: a7) :: b where
  ArgAcc7 f HNil                      acc x1 x2 x3 x4 x5 x6 x7 = Apply f acc

  ArgAcc7 f (HCons (ADrop     ) args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc6 f args acc            x2 x3 x4 x5 x6 x7
  ArgAcc7 f (HCons (AUse      ) args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc6 f args (HCons x1 acc) x2 x3 x4 x5 x6 x7
  ArgAcc7 f (HCons (AApp a    ) args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f args (HCons a  acc) x1 x2 x3 x4 x5 x6 x7

  ArgAcc7 f (HCons (ARep 0 arg) args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f args                                        acc x1 x2 x3 x4 x5 x6 x7
  ArgAcc7 f (HCons (ARep 1 arg) args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f (HCons arg args)                            acc x1 x2 x3 x4 x5 x6 x7
  ArgAcc7 f (HCons (ARep n arg) args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f (HCons arg (HCons (ARep (n - 1) arg) args)) acc x1 x2 x3 x4 x5 x6 x7
  ArgAcc7 f (HCons (AThen  arg) args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f (HCons arg (HCons (AThen arg) args))        acc x1 x2 x3 x4 x5 x6 x7

type instance App1 '(x1, x2) f = App2 f x1 x2
type instance App1 '(x1, x2, x3) f = App3 f x1 x2 x3
type instance App1 '(x1, x2, x3, x4) f = App4 f x1 x2 x3 x4
type instance App1 '(x1, x2, x3, x4, x5) f = App5 f x1 x2 x3 x4 x5
type instance App1 '(x1, x2, x3, x4, x5, x6) f = App6 f x1 x2 x3 x4 x5 x6
type instance App1 '(x1, x2, x3, x4, x5, x6, x7) f = App7 f x1 x2 x3 x4 x5 x6 x7

type family CaseMaybe (x :: Maybe a) (n :: b) (f :: a_b) :: b where
  CaseMaybe Nothing   n f = n
  CaseMaybe (Just x1) n f = App1 f x1

type family CaseList (x :: [a]) (z :: b) (f :: a_as_b) :: b where
  CaseList '[]    z f = z
  CaseList (x:xs) z f = App2 f z xs

type family CaseEither (x :: Either a b) (l :: a_c) (r :: b_c) :: c where
  CaseEither (Left  x1) l r = App1 l x1
  CaseEither (Right x1) l r = App1 r x1

type CaseBool c x1 x2 = If c x1 x2

type CaseOrd c lt eq gt = OrdCond c lt eq gt

type Compared x1 x2 lt eq gt = CaseOrd (Compare x1 x2) lt eq gt

type If2 c1 x1 c2 x2 e
   = If c1 x1 (If c2 x2 e)
type If3 c1 x1 c2 x2 c3 x3 e
   = If c1 x1 (If c2 x2 (If x3 x3 e))
type If4 c1 x1 c2 x2 c3 x3 c4 x4 e
   = If c1 x1 (If c2 x2 (If x3 x3 (If c4 x4 e)))
type If5 c1 x1 c2 x2 c3 x3 c4 x4 c5 x5 e
   = If c1 x1 (If c2 x2 (If x3 x3 (If c4 x4 (If c5 x5 e))))
type If6 c1 x1 c2 x2 c3 x3 c4 x4 c5 x5 c6 x6 e
   = If c1 x1 (If c2 x2 (If x3 x3 (If c4 x4 (If c5 x5 (If c6 x6 e)))))
type If7 c1 x1 c2 x2 c3 x3 c4 x4 c5 x5 c6 x6 c7 x7 e
   = If c1 x1 (If c2 x2 (If x3 x3 (If c4 x4 (If c5 x5 (If c6 x6 (If c7 x7 e))))))

type instance App2 '(,) x1 x2 = '(x1, x2)
type instance App3 '(,,) x1 x2 x3 = '(x1, x2, x3)
type instance App4 '(,,,) x1 x2 x3 x4 = '(x1, x2, x3, x4)
type instance App5 '(,,,) x1 x2 x3 x4 x5 = '(x1, x2, x3, x4, x5)
type instance App6 '(,,,,) x1 x2 x3 x4 x5 x6 = '(x1, x2, x3, x4, x5, x6)
type instance App7 '(,,,,,) x1 x2 x3 x4 x5 x6 x7 = '(x1, x2, x3, x4, x5, x6, x7)

type instance App1 Just x = Just x
type instance App2 (:) x xs = x : xs
type instance App1 Left  x = Left  x
type instance App1 Right x = Right x

data a :+ b
type instance App2 (:+) a b = a + b
{-
data a :<> b
type instance App2 (:<>) a b = a <> b
-}
