module Data.Type.Function where

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

data ConstK a = Const a
type instance App1 (Const k) x1 = k
type instance App2 (Const k) x1 x2 = k
type instance App3 (Const k) x1 x2 x3 = k
type instance App4 (Const k) x1 x2 x3 x4 = k
type instance App5 (Const k) x1 x2 x3 x4 x5 = k
type instance App6 (Const k) x1 x2 x3 x4 x5 x6 = k
type instance App7 (Const k) x1 x2 x3 x4 x5 x6 x7 = k

-- type Error (msg :: ErrorMessage) = Const (TypeError msg)
-- doesn't make the type checker as happy when used
data ErrorK = Error ErrorMessage
type instance App1 (Error msg) x1 = TypeError msg
type instance App2 (Error msg) x1 x2 = TypeError msg
type instance App3 (Error msg) x1 x2 x3 = TypeError msg
type instance App4 (Error msg) x1 x2 x3 x4 = TypeError msg
type instance App5 (Error msg) x1 x2 x3 x4 x5 = TypeError msg
type instance App6 (Error msg) x1 x2 x3 x4 x5 x6 = TypeError msg
type instance App7 (Error msg) x1 x2 x3 x4 x5 x6 x7 = TypeError msg

{-
type Proj1 = Mk Id (Hole (Ignore (Ignore (Ignore (Ignore (Ignore (Ignore ArgEnd)))))))
type Proj2 = Mk Id (Ignore (Hole (Ignore (Ignore (Ignore (Ignore (Ignore ArgEnd)))))))
type Proj3 = Mk Id (Ignore (Ignore (Hole (Ignore (Ignore (Ignore (Ignore ArgEnd)))))))
type Proj4 = Mk Id (Ignore (Ignore (Ignore (Hole (Ignore (Ignore (Ignore ArgEnd)))))))
type Proj5 = Mk Id (Ignore (Ignore (Ignore (Ignore (Hole (Ignore (Ignore ArgEnd)))))))
type Proj6 = Mk Id (Ignore (Ignore (Ignore (Ignore (Ignore (Hole (Ignore ArgEnd)))))))
type Proj7 = Mk Id (Ignore (Ignore (Ignore (Ignore (Ignore (Ignore (Hole ArgEnd)))))))
-}

data ArgTailK f = ArgTail f
type instance App2 (ArgTail f) x1 x2 = App1 f x2
type instance App3 (ArgTail f) x1 x2 x3 = App1 f x2 x3

--type ArgTail (f :: a) = Mk f (Ignore (Hole (Hole (Hole (Hole (Hole (Hole ArgEnd)))))))

data MkK f args = Mk f args

data ArgK a  args = Arg a  args
data HoleK   args = Hole   args
data IgnoreK args = Ignore args

data ArgAccK f args acc = ArgAcc f args acc
data ArgEnd

type family ArgAccEnd (fun :: f) (acc :: as) :: b

type instance App1 (Mk f args) x1 = ArgAcc1 f args ArgEnd x1
type instance ArgAccEnd f (Arg a1 ArgEnd) = App1 f a1
type family ArgAcc1 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) :: b where
  ArgAcc1 f (Arg a  args) acc x1 = ArgAcc1 f args (Arg a acc) x1
  ArgAcc1 f (Hole   args) acc x1 = ArgAccEnd f (Arg x1 acc)
  ArgAcc1 f Holes         acc x1 = ArgAccEnd f (Arg x1 acc)
  ArgAcc1 f (Ignore args) acc x1 = ArgAccEnd f acc
  ArgAcc1 f IgnoreRest    acc x1 = ArgAccEnd f acc

type instance App2 (Mk f args) x1 x2 = ArgAcc2 f args ArgEnd x1 x2
type instance ArgAccEnd f (Arg a2 (Arg a1 ArgEnd)) = App2 f a1 a2
type family ArgAcc2 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) :: b where
  ArgAcc2 f (Arg a  args) acc x1 x2 = ArgAcc2 f args   (Arg a  acc) x1 x2
  ArgAcc2 f (Hole   args) acc x1 x2 = ArgAcc1 f args   (Arg x1 acc) x2
  ArgAcc2 f Holes         acc x1 x2 = ArgAcc1 f Holes  (Arg x1 acc) x2
  ArgAcc2 f (Ignore args) acc x1 x2 = ArgAcc1 f args   acc          x2
  ArgAcc2 f ArgEnd        acc x1 x2 = ArgAcc1 f ArgEnd acc          x2

type instance App3 (Mk f args) x1 x2 x3 = ArgAcc3 f args ArgEnd x1 x2 x3
type instance ArgAccEnd f (Arg a3 (Arg a2 (Arg a1 ArgEnd))) = App3 f a1 a2 a3
type family ArgAcc3 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) :: b where
  ArgAcc3 f (Arg a  args) acc x1 x2 x3 = ArgAcc3 f args   (Arg a  acc) x1 x2 x3
  ArgAcc3 f (Hole   args) acc x1 x2 x3 = ArgAcc2 f args   (Arg x1 acc) x2 x3
  ArgAcc3 f Holes         acc x1 x2 x3 = ArgAcc2 f Holes  (Arg x1 acc) x2 x3
  ArgAcc3 f (Ignore args) acc x1 x2 x3 = ArgAcc2 f args   acc          x2 x3
  ArgAcc3 f ArgEnd        acc x1 x2 x3 = ArgAcc2 f ArgEnd acc          x2 x3

type instance App4 (Mk f args) x1 x2 x3 x4 = ArgAcc4 f args ArgEnd x1 x2 x3 x4
type instance ArgAccEnd f (Arg a4 (Arg a3 (Arg a2 (Arg a1 ArgEnd)))) = App4 f a1 a2 a3 a4
type family ArgAcc4 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) :: b where
  ArgAcc4 f (Arg a  args) acc x1 x2 x3 x4 = ArgAcc4 f args   (Arg a acc)  x1 x2 x3 x4
  ArgAcc4 f (Hole   args) acc x1 x2 x3 x4 = ArgAcc3 f args   (Arg x1 acc) x2 x3 x4
  ArgAcc4 f Holes         acc x1 x2 x3 x4 = ArgAcc3 f Holes  (Arg x1 acc) x2 x3 x4
  ArgAcc4 f (Ignore args) acc x1 x2 x3 x4 = ArgAcc3 f args   acc          x2 x3 x4
  ArgAcc4 f ArgEnd        acc x1 x2 x3 x4 = ArgAcc3 f ArgEnd acc          x2 x3 x4

type instance App5 (Mk f args) x1 x2 x3 x4 x5 = ArgAcc5 f args ArgEnd x1 x2 x3 x4 x5
type instance ArgAccEnd f (Arg a5 (Arg a4 (Arg a3 (Arg a2 (Arg a1 ArgEnd))))) = App5 f a1 a2 a3 a4 a5
type family ArgAcc5 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5) :: b where
  ArgAcc5 f (Arg a  args) acc x1 x2 x3 x4 x5 = ArgAcc5 f args   (Arg a acc)  x1 x2 x3 x4 x5
  ArgAcc5 f (Hole   args) acc x1 x2 x3 x4 x5 = ArgAcc4 f args   (Arg x1 acc) x2 x3 x4 x5
  ArgAcc5 f Holes         acc x1 x2 x3 x4 x5 = ArgAcc4 f Holes  (Arg x1 acc) x2 x3 x4 x5
  ArgAcc5 f (Ignore args) acc x1 x2 x3 x4 x5 = ArgAcc4 f args   acc          x2 x3 x4 x5
  ArgAcc5 f ArgEnd        acc x1 x2 x3 x4 x5 = ArgAcc4 f ArgEnd acc          x2 x3 x4 x5

type instance App6 (Mk f args) x1 x2 x3 x4 x5 x6 = ArgAcc5 f args ArgEnd x1 x2 x3 x4 x5 x6
type instance ArgAccEnd f (Arg a6 (Arg a5 (Arg a4 (Arg a3 (Arg a2 (Arg a1 ArgEnd)))))) = App6 f a1 a2 a3 a4 a5 a6
type family ArgAcc6 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5) (x6 :: a6) :: b where
  ArgAcc6 f (Arg a  args) acc x1 x2 x3 x4 x5 x6 = ArgAcc6 f args   (Arg a acc)  x1 x2 x3 x4 x5 x6
  ArgAcc6 f (Hole   args) acc x1 x2 x3 x4 x5 x6 = ArgAcc5 f args   (Arg x1 acc) x2 x3 x4 x5 x6
  ArgAcc6 f Holes         acc x1 x2 x3 x4 x5 x6 = ArgAcc5 f Holes  (Arg x1 acc) x2 x3 x4 x5 x6
  ArgAcc6 f (Ignore args) acc x1 x2 x3 x4 x5 x6 = ArgAcc5 f args   acc          x2 x3 x4 x5 x6
  ArgAcc6 f ArgEnd        acc x1 x2 x3 x4 x5 x6 = ArgAcc5 f ArgEnd acc          x2 x3 x4 x5 x6

type instance App7 (Mk f args) x1 x2 x3 x4 x5 x6 x7 = ArgAcc5 f args ArgEnd x1 x2 x3 x4 x5 x6 x7
type instance ArgAccEnd f (Arg a7 (Arg a6 (Arg a5 (Arg a4 (Arg a3 (Arg a2 (Arg a1 ArgEnd))))))) = App6 f a1 a2 a3 a4 a5 a6 a7
type family ArgAcc7 (fun :: f) (args :: argdesc) (acc :: as) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5) (x6 :: a6) (x7 :: a7) :: b where
  ArgAcc7 f (Arg a  args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc7 f args (Arg a acc)    x1 x2 x3 x4 x5 x6 x7
  ArgAcc7 f (Hole   args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc6 f args (Arg x1 acc)   x2 x3 x4 x5 x6 x7
  ArgAcc7 f Holes         acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc6 f Holes  (Arg x1 acc) x2 x3 x4 x5 x6 x7
  ArgAcc7 f (Ignore args) acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc6 f args acc            x2 x3 x4 x5 x6 x7
  ArgAcc7 f ArgEnd        acc x1 x2 x3 x4 x5 x6 x7 = ArgAcc6 f ArgEnd acc          x2 x3 x4 x5 x6 x7

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
