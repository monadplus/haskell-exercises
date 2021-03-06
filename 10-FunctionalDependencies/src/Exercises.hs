{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Exercises where

import Data.Kind (Type)
import GHC.TypeLits hiding (Nat(..))
import GHC.Generics (Generic (..), (:+:), (:*:))
import qualified GHC.Generics as G




{- ONE -}

-- | Recall an old friend, the 'Newtype' class:

--class Newtype (new :: Type) (old :: Type) where
  --wrap   :: old -> new
  --unwrap :: new -> old

-- | a. Can we add a functional dependency to this class?
class Newtype (new :: Type) (old :: Type) | new -> old where
  wrap   :: old -> new
  unwrap :: new -> old

-- | b. Why can't we add two?
-- Why would we want that ?? It's useful to have several newtypes for the same base type.




{- TWO -}

-- | Let's go back to a problem we had in the last exercise, and imagine a very
-- simple cache in IO. Uncomment the following:

--class CanCache (entity :: Type) (index :: Type) where
 --store :: entity -> IO ()
 --load  :: index -> IO (Maybe entity)

-- | a. Uh oh - there's already a problem! Any @entity@ type should have a
-- fixed type of id/@index@, though... if only we could convince GHC... Could
-- you have a go?

--class CanCache (entity :: Type) (index :: Type) | entity -> index where
 --store :: entity -> IO ()
 --load  :: index -> IO (Maybe entity)

-- | b. @IO@ is fine, but it would be nice if we could choose the functor when
-- we call @store@ or @load@... can we parameterise it in some way?

class CanCache (entity :: Type) (index :: Type) (f :: Type -> Type)
  | entity -> index where
 store :: entity -> f ()
 load  :: index -> f (Maybe entity)

-- | c. Is there any sort of functional dependency that relates our
-- parameterised functor to @entity@ or @index@? If so, how? If not, why not?

-- You could add one but it's better to leave the choice free.
-- For example, you may want to use one functor for pro and another for testing.




{- THREE -}

-- | Let's re-introduce one of our old favourites:
data Nat = Z | S Nat

-- | When we did our chapter on @TypeFamilies@, we wrote an @Add@ family to add
-- two type-level naturals together. If we do a side-by-side comparison of the
-- equivalent "class-based" approach:

class       Add  (x :: Nat) (y :: Nat) (z :: Nat) | x y -> z
type family Add' (x :: Nat) (y :: Nat)    :: Nat

-- | We see here that there are parallels between classes and type families.
-- Type families produce a result, not a constraint, though we could write
-- @Add' x y ~ z => ...@ to mean the same thing as @Add x y z => ...@. Also,
-- the result of a type family is determined by its inputs - something we can
-- express as a functional dependency!

-- | a. Write the two required instances for the 'Add' class by
-- pattern-matching on the first argument. Remember that instances can have
-- constraints, and this is how we do recursion!

instance Add 'Z y y
instance (Add x y z) => Add ('S x) y ('S z)

-- | b. By our analogy, a type family has only "one functional dependency" -
-- all its inputs to its one output. Can we write _more_ functional
-- dependencies for @Add@? Aside from @x y -> z@?

-- y x -> z -- Commutative

-- | c. We know with addition, @x + y = z@ implies @y + x = z@ and @z - x = y@.
-- This should mean that any pair of these three variables should determine the
-- other! Why couldn't we write all the possible functional dependencies that
-- /should/ make sense?

-- We can't express the functional dependency z - x = y. The following are not equivalent to the previous property.
-- z x -> y
-- z y -> x


{- FOUR -}

data Proxy (a :: k) = Proxy

-- | As we all know, type signatures are /not/ documentation. This is really
-- because the names of types are far too confusing. To that end, we can give
-- our types friendlier names to make the coding experience less intimidating:

class (x :: k) `IsNamed` (label :: Symbol) | x -> label where
  fromName :: Proxy x   -> Proxy label
  fromName _ = Proxy

  toName :: Proxy label -> Proxy x
  toName _ = Proxy

-- | Now we have this class, we can get to work!

instance Int   `IsNamed` "Dylan"
--instance Int   `IsNamed` "Nathan"
instance IO    `IsNamed` "Barbara"
instance Float `IsNamed` "Kenneth"

-- | a. In our glorious new utopia, we decide to enact a law that says, "No two
-- types shall have the same name". Similarly, "No type shall have two names".
-- Is there a way to get GHC to help us uphold the law?

-- | b. Write the identity function restricted to types named "Kenneth".
id' :: (a `IsNamed` "Kenneth") => a -> a
id' = id

-- | c. Can you think of a less-contrived reason why labelling certain types
-- might be useful in real-world code?

-- 1. Authenticated resources

-- It might be useful, for example, if we want to produce some sort of
-- language-independent description of data structures. If our description (for
-- example, postgres, or some IDL) refers to "Number", we might want to link
-- that in some way to 'Double'.



{- FIVE -}

-- | Here's a fun little class:
--class Omnipresent (r :: Symbol)

-- | Here's a fun little instance:
--instance Omnipresent "Tom!"

-- | a. Is there a way to enforce that no other instance of this class can ever
-- exist? Do we /need/ variables on the left-hand side of a functional
-- dependency arrow?

--class Omnipresent (r :: Symbol) | -> r
--instance Omnipresent "Tom!"
--instance Omnipresent "John!"

-- | b. Can you think of a time you would ever want this guarantee? Is this
-- "trick" something you can think of a practical reason for doing? Perhaps if
-- we added a method to the class? (Very much an open question).

-- Not now...
-- A useful method could be unlifting the Symbol to the value level.

-- | c. Add another similarly-omnipresent parameter to this type class.

class Omnipresent (r :: Symbol) (s :: Symbol) | -> r s
instance Omnipresent "Tom" "Riddle"
--instance Omnipresent "Tom" "Rddl"
--instance Omnipresent "To" "Rddle"




{- SIX -}

-- | You knew it was coming, didn't you?

data HList (xs :: [Type]) where
  HNil  :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

data SNat (n :: Nat) where
  SZ ::           SNat  'Z
  SS :: SNat n -> SNat ('S n)

-- | a. Write a function (probably in a class) that takes an 'SNat' and an
-- 'HList', and returns the value at the 'SNat''s index within the 'HList'.

class HIndex (ts :: [Type]) (n :: Nat) (v :: Type) | ts n -> v where
  (!!!) :: HList ts -> SNat n -> v

instance HIndex (x ': xs) 'Z x where
  (!!!) (HCons x _) SZ = x

instance (HIndex xs n x) => HIndex (z ': xs) ('S n) x where
  (!!!) (HCons _ xs) (SS n) = xs !!! n

instance ( TypeError
           ( Text "Index out of bounds."
           )
         ) => HIndex '[] n () where
           (!!!) = undefined

-- >>> xs = HCons ("hello"::String) (HCons (1::Int) HNil)
-- >>> xs !!! SZ
-- "hello"
-- >>> xs !!! (SS SZ)
-- 1
-- >>> xs !!! (SS (SS SZ))
-- error "Index out of bounds".

-- | b. Add the appropriate functional dependency.

-- | c. Write a custom type error!

-- | d. Implement 'take' for the 'HList'.
class Take (is :: [Type]) (n :: Nat) (os :: [Type]) | is n -> os where
  htake :: SNat n -> HList is -> HList os

instance Take is 'Z '[] where
  htake SZ _ = HNil

instance Take '[] n '[] where
  htake _ HNil = HNil

instance (Take is n os)
    => Take (x ': is) ('S n) (x ': os) where
  htake (SS n) (HCons x xs) = HCons x (htake n xs)

-- >>> let hlist = HCons True (HCons "hello" (HCons (1::Int) HNil))
--
-- >>> let hlist2 = htake (SS (SS SZ)) hlist
-- hlist2 :: HList '[Bool, [Char]]
--
-- >>> let hlist3 = htake (SS (SS (SS (SS (SS SZ))))) hlist
-- hlist3 :: HList '[Bool, [Char], Int]

{- SEVEN -}

-- | Recall our variant type:

data Variant (xs :: [Type]) where
  Here  ::         x  -> Variant (x ': xs)
  There :: Variant xs -> Variant (y ': xs)

-- | We previously wrote a function to "inject" a value into a variant:

class Inject (x :: Type) (xs :: [Type]) where
  inject :: x -> Variant xs

instance Inject x (x ': xs) where
  inject = Here

instance {-# INCOHERENT #-} Inject x xs => Inject x (z ': xs) where
  inject = There . inject

-- | Write a function to "project" a value /out of/ a variant. In other words,
-- I would like a function that takes a proxy of a type, a variant containing
-- that type, and returns /either/ a value of that type /or/ the variant
-- /excluding/ that type:
--
-- @
--   project (Proxy :: Proxy Bool) (inject True :: Variant '[Int, String, Bool])
--     === Left Bool :: Either Bool (Variant '[Int, String])
-- @

class Project (x :: Type) (xs :: [Type]) (rs :: [Type]) where
  project :: Proxy x -> Variant xs -> Either x (Variant rs)

instance Project x (x ': xs) xs where
  project _ (Here x)   = Left x
  project _ (There xs) = error "Impossible" -- Right xs -- This will only happens when the Variant is wrong.

instance (Project x xs rs) => Project x (z ': xs) (z ': rs) where
  project _ (Here _)   = error "Impossible!"
  project p (There xs) = There <$> project p xs

-- >>> project (Exercises.Proxy :: Exercises.Proxy Bool) (inject True :: Variant '[Int, String, Bool])
-- Left Bool :: Either Bool (Variant '[Int, String])
-- >>> project (Exercises.Proxy :: Exercises.Proxy String) (inject True :: Variant '[Int, String, Bool])
-- Right ...




{- EIGHT -}

-- | It would be nice if I could update a particular index of an HList by
-- providing an index and a (possibly-type-changing) function. For example:
--
-- @
--   update SZ length (HCons True (HCons "Hello" HNil))
--     === HCons True (HCons 5 HNil)
-- @

-- | Write the type class required to implement this function, along with all
-- its instances and functional dependencies.

class Update (i :: Nat) (s :: [Type]) (t :: [Type]) (a :: Type) (b :: Type)
    | s i -> a, t i -> b, i s b -> t, i t a -> s where
  update :: SNat i -> (a -> b) -> HList s -> HList t

instance Update 'Z (a ': s) (b ': s) a b where
  update SZ f (HCons a s) = HCons (f a) s

instance (Update i s t a b)
    => Update ('S i) (x ': s) (x ': t) a b where
      update (SS i) f (HCons x s) = HCons x (update i f s)

-- >>> let hlist = HCons True (HCons "Hello" HNil); hlist :: HList '[Bool, [Char]]
-- >>> hlist2 = update (SS SZ) length hlist
-- HCons True (HCons 5 HNil)


-- The error messages are not the best. For example,
--
-- >>> hlist2 = update SZ length hlist




{- NINE -}

-- | If you've made it this far, you're more than capable of digesting and
-- understanding some advanced GHC docs! Read the documentation at
-- http://hackage.haskell.org/package/base-4.12.0.0/docs/GHC-Generics.html, and
-- keep going until you hit 'Generic1' - we won't worry about that today.

-- | We can write a little function to get the name of a type as a type-level
-- symbol like so:

class NameOf (x :: Type) (name :: Symbol) | x -> name
instance GNameOf (Rep x) name => NameOf x name
-- >>> foo :: (NameOf Int s, KnownSymbol s) => IO (); foo = print $ symbolVal (Proxy @s)

-- | We then have to implement this class that examines the generic tree...
class GNameOf (rep :: Type -> Type) (name :: Symbol) | rep -> name
instance GNameOf (G.D1 ('G.MetaData name a b c) d) name

-- | Write a function to get the names of the constructors of a type as a
-- type-level list of symbols.
class ConstructorsOf (x :: Type) (names :: [Symbol]) | x -> names
instance GConstructorsOf (Rep x) names => ConstructorsOf x names

class GConstructorsOf (rep :: Type -> Type) (names :: [Symbol]) | rep -> names
-- Data Type constructor
instance GConstructorsOf inner name => GConstructorsOf (G.D1 meta inner) name
-- Constructor
instance GConstructorsOf (G.C1 ('G.MetaCons name x y) a) '[name]
-- Product constructors.
instance (GConstructorsOf l lNames, GConstructorsOf r rNames, Concat lNames rNames names)
  => GConstructorsOf (l :*: r) names

class Concat (xs :: [k]) (ys :: [k]) (zs :: [k]) | xs ys -> zs
instance Concat '[] ys ys
instance Concat xs ys zs => Concat (x ': xs) ys (x ': zs)

{- TEN -}

-- In the standard library, we have a series of @liftA*@ functions, such as
-- 'liftA2', 'liftA3', 'liftA4'... wouldn't it be nice if we just had /one/
-- function called 'lift' that generalised all these?
--
liftA1 :: Applicative f => (a -> b) -> f a -> f b
liftA1 = lift
--
liftA2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 = lift
--
--
liftA3 :: Applicative f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA3 = lift

-- Write this function, essentially generalising the f <$> a <*> b <*> c...
-- pattern. It may help to see it as pure f <*> a <*> b <*> c..., and start
-- with a function like this:

lift :: (Applicative f, Lift f i o) => i -> o
lift = lift' . pure

-- @class Lift f i o ... where lift' :: ...@ is your job! If you get this
-- right, perhaps with some careful use of @INCOHERENT@, equality constraints,
-- and functional dependencies, you should be able to get some pretty amazing
-- type inference:
--
-- >>> :t lift (++)
-- lift (++) :: Applicative f => f [a] -> f [a] -> f [a]

class Lift (f :: Type -> Type) (i :: Type) (o :: Type) | f i -> o, o -> f where
  lift' :: f i -> o

instance (Applicative f, Lift f b o', o ~ (f a -> o'))
  => Lift f (a -> b) o where
    lift' fs xs = lift' (fs <*> xs)

instance {-# INCOHERENT #-} Applicative f => Lift f a (f a) where
  lift' = id
