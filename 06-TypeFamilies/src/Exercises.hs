{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeInType #-}
module Exercises where

import Data.Monoid hiding (All)
import Data.Kind (Constraint, Type)
--import GHC.TypeLits (Nat)

-- | Before we get started, let's talk about the @TypeOperators@ extension. All
-- this does is allow us to write types whose names are operators, and write
-- regular names as infix names with the backticks, as we would at the value
-- level.





{- ONE -}

data Nat = Z | S Nat

-- | a. Use the @TypeOperators@ extension to rewrite the 'Add' family with the
-- name '+':
type family (+) (x :: Nat) (y :: Nat) :: Nat where
  Z + y = y
  (S x) + y = S (x + y)

-- | b. Write a type family '**' that multiplies two naturals using '(+)'. Which
-- extension are you being told to enable? Why? -XUndeciableInstances
type family (**) (x :: Nat) (y :: Nat) :: Nat where
  Z ** _ = Z
  -- m * n, add n to itself, m times.
  (S x) ** y = y + (x ** y)

data SNat (value :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | c. Write a function to add two 'SNat' values.

add' :: SNat n -> SNat m -> SNat (n + m)
add' SZ y     = y
add' (SS x) y = SS (add' x y)



{- TWO -}

data Vector (count :: Nat) (a :: Type) where
  VNil  :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | a. Write a function that appends two vectors together. What would the size
-- of the result be?
appendV :: Vector m a -> Vector n a -> Vector (m + n) a
appendV VNil v = v
appendV (VCons a v1) v2 = VCons a (appendV v1 v2)

-- | b. Write a 'flatMap' function that takes a @Vector n a@, and a function
-- @a -> Vector m b@, and produces a list that is the concatenation of these
-- results. This could end up being a deceptively big job.

flatMap :: Vector n a -> (a -> Vector m b) -> Vector (n ** m) b
flatMap VNil _ = VNil
flatMap (VCons a v1) f = appendV (f a) (flatMap v1 f)




{- THREE -}

-- | a. More boolean fun! Write the type-level @&&@ function for booleans.
type family (b1 :: Bool) && (b2 :: Bool) :: Bool where
  'False && _ = 'False
  'True && b2 = b2

-- | b. Write the type-level @||@ function for booleans.
type family (b1 :: Bool) || (b2 :: Bool) :: Bool where
  'True  || _  = 'True
  'False || b2 = b2

-- | c. Write an 'All' function that returns @'True@ if all the values in a
-- type-level list of boleans are @'True@.
type family All (xs :: [Bool]) :: Bool where
  All '[]       = 'True
  All (b ': bs) = b && (All bs)




{- FOUR -}

-- | a. Nat fun! Write a type-level 'compare' function using the promoted
-- 'Ordering' type.
type family Compare (x :: Nat) (y :: Nat) :: Ordering where
  Compare 'Z 'Z = 'EQ
  Compare 'Z _ = 'LT
  Compare _ 'Z = 'GT
  Compare ('S n1) ('S n2) = Compare n1 n2


-- | b. Write a 'Max' family to get the maximum of two natural numbers.
type family Max (x :: Nat) (y :: Nat) :: Nat where
  Max x y = Max' (Compare x y) x y

type family Max' (ord :: Ordering) (x :: Nat) (y :: Nat) :: Nat where
  Max' 'LT _ y = y
  Max' _   x _ = x

-- | c. Write a family to get the maximum natural in a list.
type family Map (xs :: [a]) (f :: a -> b) :: [b] where
  Map '[] _ = '[]
  Map (a ': as) f = f a ': (Map as f)

type family Foldl (f :: b -> a -> b) (b' :: b) (xs :: [a]) :: b where
  Foldl _ b '[] = b
  Foldl f b (a ': as) = Foldl f (f b a) as

-- TODO: The type family ‘Max’ should have 2 arguments, but has been given none
--type family MaxList (xs :: [Nat]) :: Nat where
  --MaxList xs = Foldl Max 'Z xs



{- FIVE -}

data Tree = Empty | Node Tree Nat Tree

-- | Write a type family to insert a promoted 'Nat' into a promoted 'Tree'.

type family Insert (t :: Tree) (n :: Nat) :: Tree where
  Insert 'Empty n      = 'Node 'Empty n 'Empty
  Insert ('Node l c r) n = Insert' (Compare n c) ('Node l c r) n

type family Insert' (ord :: Ordering) (t :: Tree) (n :: Nat) :: Tree where
  Insert' 'EQ t _            = t
  Insert' 'LT ('Node l c r) n = 'Node (Insert l n) c r
  Insert' 'GT ('Node l c r) n = 'Node l c (Insert r n)
-- >>> type Tree1 = 'Node ('Node 'Empty 3 'Empty) 5 ('Node 'Empty 8 'Empty)
-- >>> :kind! Insert Tree1 7

{- SIX -}

-- | Write a type family to /delete/ a promoted 'Nat' from a promoted 'Tree'.
type family Delete (t :: Tree) (n :: Nat) :: Tree where
  Delete 'Empty _        = 'Empty
  Delete ('Node l c r) n = Delete' (Compare n c) ('Node l c r) n

type family Delete' (ord :: Ordering) (t :: Tree) (n :: Nat) :: Tree where
  Delete' 'LT ('Node l c r) n = 'Node (Delete l n) c r
  Delete' 'GT ('Node l c r) n = 'Node l c (Delete r n)
  Delete' 'EQ ('Node l c 'Empty) n = l
  Delete' 'EQ ('Node l c r) n = Constr l (Smallest r)

type family Constr (l :: Tree) (r :: (Nat, Tree)) :: Tree where
  Constr l '(c, r) = 'Node l c r

type family Smallest (t :: Tree) :: (Nat, Tree) where
  Smallest ('Node 'Empty c r) = '(c, r)
  Smallest ('Node l c r) = Smallest' (Smallest l) c r

type family Smallest' (l :: (Nat, Tree)) (c :: Nat) (r:: Tree) :: (Nat, Tree) where
  Smallest' '(min, l) c r = '(min, 'Node l c r)


-- We can use this type to write "tests" for the above. Any mention of Refl
-- will force GHC to try to unify the two type parameters. If it fails, we get
-- a type error!
data (x :: a) :~: (y :: b) where
  Refl :: a :~: a

deleteTest0 :: Delete 'Empty 'Z :~: 'Empty
deleteTest0 = Refl

deleteTest1 :: Delete (Insert 'Empty 'Z) 'Z :~: 'Empty
deleteTest1 = Refl

deleteTest2 :: Insert (Insert 'Empty 'Z) 'Z :~: Insert 'Empty 'Z
deleteTest2 = Refl

deleteTest3
   :: Insert (Insert 'Empty 'Z) ('S 'Z)
  :~: 'Node 'Empty 'Z ('Node 'Empty ('S 'Z) 'Empty)
deleteTest3 = Refl

-- In case you're interested, here's a failing test!
--deleteTest4 :: Insert 'Z 'Empty :~: 'Empty
--deleteTest4 = Refl


{- SEVEN -}

-- | With @TypeOperators@, we can use regular Haskell list syntax on the
-- type-level, which I think is /much/ tidier than anything we could define.

data HList (xs :: [Type]) where
  HNil  :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

-- | Write a function that appends two 'HList's.

type family (xs :: [a]) ++ (ys :: [a]) :: [a] where
  '[]       ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

--Won't work
--appendH :: HList xs -> HList ys -> HList zs
--appendH = error ""
appendH :: HList xs -> HList ys -> HList (xs ++ ys)
appendH HNil ys = ys
appendH (HCons x xs) ys = HCons x (appendH xs ys)


{- EIGHT -}

-- | Type families can also be used to build up constraints. There are, at this
-- point, a couple things that are worth mentioning about constraints:
--
-- - As we saw before, '()' is the empty constraint, which simply has "no
--   effect", and is trivially solved.
--
-- - Unlike tuples, constraints are "auto-flattened": ((a, b), (c, (d, ())) is
--   exactly equivalent to (a, b, c, d). Thanks to this property, we can build
--   up constraints using type families!

type family CAppend (x :: Constraint) (y :: Constraint) :: Constraint where
  CAppend x y = (x, y)

-- | a. Write a family that takes a constraint constructor, and a type-level
-- list of types, and builds a constraint on all the types.

type family Every (c :: Type -> Constraint) (x :: [Type]) :: Constraint where
  Every  _ '[]       = ()
  Every  c (t ': ts) = (c t, Every c ts)

-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.
instance (Every Show xs) => Show (HList xs) where
  show HNil = "HNil"
  show (HCons x xs) = "HCons(" ++ show x ++ "," ++ show xs ++ ")"

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?
instance (Every Eq xs) => Eq (HList xs) where
  HNil == HNil = True
  (HCons x xs) == (HCons y ys) = x == y && xs == ys
  -- HNil == (HCons _ _) = False -- redundant because '[] is not equal to x ': xs1

-- HC can't /see/ a constraint that says any particular @x@ has an 'Ord' constraint,
-- which means it can't convince itself that this will be true in the general case.
instance (Every Eq xs, Every Ord xs) => Ord (HList xs) where
  HNil `compare` HNil = EQ
  (HCons x xs) `compare` (HCons y ys) = x `compare` y <> xs `compare` ys



{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.
type family UpToN (n :: Nat) :: [Nat] where
  UpToN 'Z = '[ 'Z  ]
  UpToN ('S n) = (UpToN n) ++ '[ 'S n ]

type family Drop (n :: Nat) (xs :: [Nat]) :: [Nat] where
  Drop 'Z xs            = xs
  Drop _ '[]            = '[]
  Drop ('S n) (_ ': xs) = Drop n xs

-- | b. Write a type-level prime number sieve.

-- Source: https://wiki.haskell.org/Prime_numbers
--primesTo m = sieve [2..m]
             --where
             --sieve (x:xs) = x : sieve (xs \\ [x,x+x..m])
             --sieve [] = []

type family Sieve (n :: Nat) :: [Nat] where
  Sieve n = Sieve' (Drop N2 (UpToN n))

type family Sieve' (xs :: [Nat]) :: [Nat] where
  Sieve'       '[] = '[]
  Sieve' (x ': xs) = x ': Sieve' (DropEveryN x xs)

type family DropEveryN (n :: Nat) (xs :: [Nat]) :: [Nat] where
  DropEveryN n xs = DropEveryN' n n xs

type family DropEveryN' (x :: Nat) (n :: Nat) (xs :: [Nat]) :: [Nat] where
  DropEveryN' _ _             '[] = '[]
  DropEveryN' x ('S 'Z) ( _ ': xs) = DropEveryN' x x xs
  DropEveryN' x ('S n) (x' ': xs) = x' ': (DropEveryN' x n xs)

testDropEveryN :: DropEveryN N2 (UpToN N10) :~: '[ N0, N2, N4, N6, N8, N10 ]
testDropEveryN = Refl

type N0  = 'Z
type N1  = 'S N0
type N2  = 'S N1
type N3  = 'S N2
type N4  = 'S N3
type N5  = 'S N4
type N6  = 'S N5
type N7  = 'S N6
type N8  = 'S N7
type N9  = 'S N8
type N10 = 'S N9


test :: Sieve N10 :~: '[ N2, N3, N5, N7 ]
test = Refl

-- | c. Why is this such hard work?

-- Disclaimer: answer copied from the solutions

-- I think it boils down to a few things:
--
-- * No let-binding at the type level.
--
-- * No higher-order functions - I can't write higher-order helpers without
--   running into complaints about type families not having all their
--   arguments. Recent work on unsaturated type families (type families without
--   all their arguments) promises a solution to this, though!
--
-- * Syntax!
