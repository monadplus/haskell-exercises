{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeInType #-}
module Exercises where

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
  Delete 'Empty        _ = 'Empty
  Delete ('Node l c r) n = Delete' (Compare n c) ('Node l c r) n

type family Delete' (ord :: Ordering) (t :: Tree) (n :: Nat) :: Tree where
  Delete' 'LT ('Node l c r)      n = 'Node (Delete l n) c r
  Delete' 'GT ('Node l c r)      n = 'Node l c (Delete r n)
  Delete' 'EQ ('Node 'Empty _ r) _ = r
  Delete' 'EQ ('Node l _ r)      n = Constr (Biggest l) r

-- Reconstruct the Node from the largest value from the l and its tree.
type family Constr (l :: (Nat, Tree)) (r :: Tree) :: Tree where
  Constr '(c, l) r = 'Node l c r

-- Find the largest node, remove the value and retrieve the tree.
type family Biggest (t :: Tree) :: (Nat,Tree) where
  Biggest ('Node l c 'Empty) = '(c, l)
  -- Biggest value is on r
  -- After we found it we must reconstruct the returning Tree.
  Biggest ('Node l c r) = Constr' l c (Biggest r)

type family Constr' (l :: Tree) (c :: Nat) (r :: (Nat, Tree)) :: (Nat, Tree) where
  Constr' l c '(max, r) = '(max, ('Node l c r))

-- We can use this type to write "tests" for the above. Any mention of Refl
-- will force GHC to try to unify the two type parameters. If it fails, we get
-- a type error!
data (x :: Tree) :~: (y :: Tree) where
  Refl :: x :~: x

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
  -- ...

-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?





{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.

-- | b. Write a type-level prime number sieve.

-- | c. Why is this such hard work?
