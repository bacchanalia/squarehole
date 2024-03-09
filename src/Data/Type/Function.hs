module Data.Type.Function where

import Data.Type.Bool
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

type Const (x :: a) = Id :$ AThen ADrop :$ x :$ AEnd
type AProj (n :: Nat) = Id :$ ARep (n - 1) ADrop :$ AUse :$ AEnd
type ATail (fun :: f) = fun :$ ADrop :$ AThen AUse :$ AEnd

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

infixr 0 :$
data (x :: a) :$ (xs :: b)

data AEnd

data AUse
data ADrop
data ARepK a = ARep Nat a
data AThen a
type family Apply (fun :: f) (acc :: as) :: b

type family ArgAcc0 (fun :: f) (args :: argdesc) (acc :: as) :: b where
  ArgAcc0 f AEnd                 acc = Apply f acc

  ArgAcc0 f (ARep 0 arg :$ args) acc = ArgAcc0 f args                              acc
  ArgAcc0 f (ARep 1 arg :$ args) acc = ArgAcc0 f (arg :$ args)                     acc
  ArgAcc0 f (ARep n arg :$ args) acc = ArgAcc0 f (arg :$ ARep (n - 1) arg :$ args) acc
  ArgAcc0 f (AThen  arg :$ args) acc = ArgAcc0 f args                              acc

  ArgAcc0 f (ADrop      :$ args) acc = ArgAcc0 f args acc
  ArgAcc0 f (AUse       :$ args) acc = ArgAcc0 f args acc
  ArgAcc0 f (a          :$ args) acc = ArgAcc0 f args (a :$ acc)

type instance App1 (f :$ args) x1 = ArgAcc1 f args AEnd x1
type instance Apply f (a1 :$ AEnd) = App1 f a1
type family ArgAcc1 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) :: b where
  ArgAcc1 f AEnd                 acc x1 = Apply f acc

  ArgAcc1 f (ARep 0 arg :$ args) acc x1 = ArgAcc1 f args                              acc x1
  ArgAcc1 f (ARep 1 arg :$ args) acc x1 = ArgAcc1 f (arg :$ args)                     acc x1
  ArgAcc1 f (ARep n arg :$ args) acc x1 = ArgAcc1 f (arg :$ ARep (n - 1) arg :$ args) acc x1
  ArgAcc1 f (AThen  arg :$ args) acc x1 = ArgAcc1 f (arg :$ AThen arg        :$ args) acc x1

  ArgAcc1 f (ADrop      :$ args) acc x1 = ArgAcc0 f args acc
  ArgAcc1 f (AUse       :$ args) acc x1 = ArgAcc0 f args (x1 :$ acc)
  ArgAcc1 f (a          :$ args) acc x1 = ArgAcc1 f args (a  :$ acc) x1

type instance App2 (f :$ args) x1 x2 = ArgAcc2 f args AEnd x1 x2
type instance Apply f (a2 :$ a1 :$ AEnd) = App2 f a1 a2
type family ArgAcc2 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) :: b where
  ArgAcc2 f AEnd                 acc x1 x2 = Apply f acc

  ArgAcc2 f (ARep 0 arg :$ args) acc x1 x2 = ArgAcc2 f args                              acc x1 x2
  ArgAcc2 f (ARep 1 arg :$ args) acc x1 x2 = ArgAcc2 f (arg :$ args)                     acc x1 x2
  ArgAcc2 f (ARep n arg :$ args) acc x1 x2 = ArgAcc2 f (arg :$ ARep (n - 1) arg :$ args) acc x1 x2
  ArgAcc2 f (AThen  arg :$ args) acc x1 x2 = ArgAcc2 f (arg :$ AThen arg        :$ args) acc x1 x2

  ArgAcc2 f (ADrop      :$ args) acc x1 x2 = ArgAcc1 f args acc         x2
  ArgAcc2 f (AUse       :$ args) acc x1 x2 = ArgAcc1 f args (x1 :$ acc) x2
  ArgAcc2 f (a          :$ args) acc x1 x2 = ArgAcc2 f args (a  :$ acc) x1 x2

type instance App3 (f :$ args) x1 x2 x3 = ArgAcc3 f args AEnd x1 x2 x3
type instance Apply f (a3 :$ a2 :$ a1 :$ AEnd) = App3 f a1 a2 a3
type family ArgAcc3 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) :: b where
  ArgAcc3 f AEnd                 acc x1 x2 x3 = Apply f acc

  ArgAcc3 f (ARep 0 arg :$ args) acc x1 x2 x3 = ArgAcc3 f args                              acc x1 x2 x3
  ArgAcc3 f (ARep 1 arg :$ args) acc x1 x2 x3 = ArgAcc3 f (arg :$ args)                     acc x1 x2 x3
  ArgAcc3 f (ARep n arg :$ args) acc x1 x2 x3 = ArgAcc3 f (arg :$ ARep (n - 1) arg :$ args) acc x1 x2 x3
  ArgAcc3 f (AThen  arg :$ args) acc x1 x2 x3 = ArgAcc3 f (arg :$ AThen arg        :$ args) acc x1 x2 x3

  ArgAcc3 f (ADrop      :$ args) acc x1 x2 x3 = ArgAcc2 f args acc         x2 x3
  ArgAcc3 f (AUse       :$ args) acc x1 x2 x3 = ArgAcc2 f args (x1 :$ acc) x2 x3
  ArgAcc3 f (a          :$ args) acc x1 x2 x3 = ArgAcc3 f args (a  :$ acc) x1 x2 x3

type instance App4 (f :$ args) x1 x2 x3 x4 = ArgAcc4 f args AEnd x1 x2 x3 x4
type instance Apply f (a4 :$ a3 :$ a2 :$ a1 :$ AEnd) = App4 f a1 a2 a3 a4
type family ArgAcc4 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) :: b where
  ArgAcc4 f AEnd                 acc x1 x2 x3 x4 = Apply f acc

  ArgAcc4 f (ARep 0 arg :$ args) acc x1 x2 x3 x4 = ArgAcc4 f args                              acc x1 x2 x3 x4
  ArgAcc4 f (ARep 1 arg :$ args) acc x1 x2 x3 x4 = ArgAcc4 f (arg :$ args)                     acc x1 x2 x3 x4
  ArgAcc4 f (ARep n arg :$ args) acc x1 x2 x3 x4 = ArgAcc4 f (arg :$ ARep (n - 1) arg :$ args) acc x1 x2 x3 x4
  ArgAcc4 f (AThen  arg :$ args) acc x1 x2 x3 x4 = ArgAcc4 f (arg :$ AThen arg        :$ args) acc x1 x2 x3 x4

  ArgAcc4 f (ADrop      :$ args) acc x1 x2 x3 x4 = ArgAcc3 f args acc         x2 x3 x4
  ArgAcc4 f (AUse       :$ args) acc x1 x2 x3 x4 = ArgAcc3 f args (x1 :$ acc) x2 x3 x4
  ArgAcc4 f (a          :$ args) acc x1 x2 x3 x4 = ArgAcc4 f args (a  :$ acc) x1 x2 x3 x4

type instance App5 (f :$ args) x1 x2 x3 x4 x5 = ArgAcc5 f args AEnd x1 x2 x3 x4 x5
type instance Apply f (a5 :$ a4 :$ a3 :$ a2 :$ a1 :$ AEnd) = App5 f a1 a2 a3 a4 a5
type family ArgAcc5 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5) :: b where
  ArgAcc5 f AEnd                 acc x1 x2 x3 x4 x5 = Apply f acc

  ArgAcc5 f (ARep 0 arg :$ args) acc x1 x2 x3 x4 x5 = ArgAcc5 f args                              acc x1 x2 x3 x4 x5
  ArgAcc5 f (ARep 1 arg :$ args) acc x1 x2 x3 x4 x5 = ArgAcc5 f (arg :$ args)                     acc x1 x2 x3 x4 x5
  ArgAcc5 f (ARep n arg :$ args) acc x1 x2 x3 x4 x5 = ArgAcc5 f (arg :$ ARep (n - 1) arg :$ args) acc x1 x2 x3 x4 x5
  ArgAcc5 f (AThen  arg :$ args) acc x1 x2 x3 x4 x5 = ArgAcc5 f (arg :$ AThen arg        :$ args) acc x1 x2 x3 x4 x5

  ArgAcc5 f (ADrop      :$ args) acc x1 x2 x3 x4 x5 = ArgAcc4 f args acc         x2 x3 x4 x5
  ArgAcc5 f (AUse       :$ args) acc x1 x2 x3 x4 x5 = ArgAcc4 f args (x1 :$ acc) x2 x3 x4 x5
  ArgAcc5 f (a          :$ args) acc x1 x2 x3 x4 x5 = ArgAcc5 f args (a  :$ acc) x1 x2 x3 x4 x5

type instance App6 (f :$ args) x1 x2 x3 x4 x5 x6 = ArgAcc6 f args AEnd x1 x2 x3 x4 x5 x6
type instance Apply f (a6 :$ a5 :$ a4 :$ a3 :$ a2 :$ a1 :$ AEnd) = App6 f a1 a2 a3 a4 a5 a6
type family ArgAcc6 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5) (x6 :: a6) :: b where
  ArgAcc6 f AEnd                 acc x1 x2 x3 x4 x5 x6 = Apply f acc

  ArgAcc6 f (ARep 0 arg :$ args) acc x1 x2 x3 x4 x5 x6 = ArgAcc6 f args                              acc x1 x2 x3 x4 x5 x6
  ArgAcc6 f (ARep 1 arg :$ args) acc x1 x2 x3 x4 x5 x6 = ArgAcc6 f (arg :$ args)                     acc x1 x2 x3 x4 x5 x6
  ArgAcc6 f (ARep n arg :$ args) acc x1 x2 x3 x4 x5 x6 = ArgAcc6 f (arg :$ ARep (n - 1) arg :$ args) acc x1 x2 x3 x4 x5 x6
  ArgAcc6 f (AThen  arg :$ args) acc x1 x2 x3 x4 x5 x6 = ArgAcc6 f (arg :$ AThen arg        :$ args) acc x1 x2 x3 x4 x5 x6

  ArgAcc6 f (ADrop      :$ args) acc x1 x2 x3 x4 x5 x6 = ArgAcc5 f args acc         x2 x3 x4 x5 x6
  ArgAcc6 f (AUse       :$ args) acc x1 x2 x3 x4 x5 x6 = ArgAcc5 f args (x1 :$ acc) x2 x3 x4 x5 x6
  ArgAcc6 f (a          :$ args) acc x1 x2 x3 x4 x5 x6 = ArgAcc6 f args (a  :$ acc) x1 x2 x3 x4 x5 x6

type instance App7 (f :$ args) x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f args AEnd x1 x2 x3 x4 x5 x6 x7
type instance Apply f (a7 :$ a6 :$ a5 :$ a4 :$ a3 :$ a2 :$ a1 :$ AEnd) = App7 f a1 a2 a3 a4 a5 a6 a7
type family ArgAcc7 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5) (x6 :: a6) (x7 :: a7) :: b where
  ArgAcc7 f AEnd                 acc x1 x2 x3 x4 x5 x6 x7 = Apply f acc

  ArgAcc7 f (ARep 0 arg :$ args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f args                              acc x1 x2 x3 x4 x5 x6 x7
  ArgAcc7 f (ARep 1 arg :$ args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f (arg :$ args)                     acc x1 x2 x3 x4 x5 x6 x7
  ArgAcc7 f (ARep n arg :$ args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f (arg :$ ARep (n - 1) arg :$ args) acc x1 x2 x3 x4 x5 x6 x7
  ArgAcc7 f (AThen  arg :$ args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f (arg :$ AThen arg        :$ args) acc x1 x2 x3 x4 x5 x6 x7

  ArgAcc7 f (ADrop      :$ args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc6 f args acc         x2 x3 x4 x5 x6 x7
  ArgAcc7 f (AUse       :$ args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc6 f args (x1 :$ acc) x2 x3 x4 x5 x6 x7
  ArgAcc7 f (a          :$ args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f args (a  :$ acc) x1 x2 x3 x4 x5 x6 x7

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
