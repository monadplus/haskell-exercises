{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-} -- Linee 75
{-# LANGUAGE TypeApplications #-}
module Exercises where -- ^ This is starting to look impressive, right?

import Data.Kind (Constraint, Type)
import Data.Monoid ((<>), Sum(..))
import Data.Proxy

-- | Just a quick one today - there really isn't much to cover when we talk
-- about ConstraintKinds, as it's hopefully quite an intuitive extension: we're
-- just extending the set of things that we can use as constraints to include
-- type parameters!

-- ConstraintKinds: https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#extension-ConstraintKinds



{- ONE -}

-- | Here's a super uninteresting list, which comes with an unfortunate
-- restriction: everything in the list must have the same exact type.

data List a = Nil | Cons a (List a)

-- | We can generalise this data structure to a /constrained list/, in which we
-- say, instead of "every value has this type", we say, "every value's type
-- satisfies this constraint".

-- | a. Do it! Think about the @Nil@ and @Cons@ cases separately; which
-- constraints can the @Nil@ case satisfy?

data ConstrainedList (c :: Type -> Constraint) where
  CNil :: ConstrainedList c -- ConstrainedList (const ())
  CCons :: c a => a -> ConstrainedList c -> ConstrainedList c

-- | b. Using what we know about RankNTypes, write a function to fold a
-- constrained list. Note that we'll need a folding function that works /for
-- all/ types who implement some constraint @c@. Wink wink, nudge nudge.

foldConstrainedList
  :: Monoid m
  => (forall x. c x => x -> m)
  -> ConstrainedList c
  -> m
foldConstrainedList _ CNil = mempty
foldConstrainedList f (CCons x xs) = f x <> foldConstrainedList f xs -- brings c x into scope

foldlConstrainedList
  :: forall c r. (forall x. c x => r -> x -> r)
  -> r
  -> ConstrainedList c
  -> r
foldlConstrainedList f r = go r
  where
    go r CNil = r
    go r (CCons x xs) = go (f r x) xs

-- | Often, I'll want to constrain a list by /multiple/ things. The problem is
-- that I can't directly write multiple constraints into my type, because the
-- kind of @(Eq, Ord)@ isn't @Type -> Constraint@ - it's actually a kind error!   :kind! (Eq, Int)

-- | There is hope, however: a neat trick we can play is to define a new class,
-- whose super classes are all the constraints we require. We can then write an
-- instance for any a who satisfies these constraints. Neat, right?

-- | c. Write this class instance so that we can have a constraint that
-- combines `Monoid a` and `Show a`. What other extension did you need to
-- enable? Why?

class (Show a , Monoid a) => ShowMonoid a
instance (Show a, Monoid a) => ShowMonoid a
-- UndecidableInstances is required because nothing is getting "smaller" - when
-- GHC encounters this constraint, it ends up with more things to solve! This
-- means that GHC's (limited) termination checker can't be convinced that we'll
-- ever terminate.


-- | What can we now do with this constrained list that we couldn't before?
-- There are two opportunities that should stand out!

-- We can show everything in it, and we can fill it with 'mempty'.
-- We can't write a monoid instance, because we have no way of telling that two
-- constrained lists contain the /same/ monoids. :(

-- >>> xs = CCons (Sum 1) (CCons (Sum 2) CNil) :: ConstrainedList ShowMonoid
-- >>> foldConstrainedList show xs
-- >>> foldConstrainedList (const mempty) xs




{- TWO -}

-- | Recall our HList:

data HList (xs :: [Type]) where
  HNil  :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

-- | Ideally, we'd like to be able to fold over this list in some way, ideally
-- by transforming every element into a given monoid according to the interface
-- of some constraint. To do that, though, we'd need to know that everything in
-- the list implemented a given constraint... if only we had a type family for
-- this...

type family CAll (c :: Type -> Constraint) (xs :: [Type]) :: Constraint where
  CAll _       '[] = ()
  CAll c (x ': xs) = (c x, CAll c xs)

data TCProxy (c :: Type -> Constraint) where
  TCProxy :: TCProxy c

-- | a. Write this fold function. I won't give any hints to the definition, but
-- we will probably need to call it like this:

fold
  :: (Monoid m, CAll c xs)
  => TCProxy c
  -> (forall x. c x => x -> m)
  -> HList xs
  -> m
fold     _ _         HNil = mempty
fold proxy f (HCons x xs) = f x <> (fold proxy f xs)

test :: CAll Show xs => HList xs -> String
test = fold (TCProxy @Show) show
-- >>> xs = HCons (1 :: Int) (HCons True (HCons "hi" HNil))
-- >>> test xs

-- | b. Why do we need the proxy to point out which constraint we're working
-- with?  What does GHC not like if we remove it?

--Could not deduce: CAll c0 xs from the context: (Monoid m, CAll c xs)
--bound by the type signature for: fold :: (Monoid m, CAll c xs) => (forall x. c x => x -> m) -> HList xs -> m
--at src/Exercises.hs:(125,6)-(128,6)

-- The type is ambiguous for GHC.

-- | We typically define foldMap like this:

foldMap :: Monoid m => (a -> m) -> [a] -> m
foldMap f = foldr (\x acc -> f x <> acc) mempty

-- | c. What constraint do we need in order to use our @(a -> m)@ function on
-- an @HList@? You may need to look into the __equality constraint__ introduced
-- by the @GADTs@ and @TypeFamilies@ extensions, written as @(~)@:

    -- * This tells GHC that @a@ and @b@ are equivalent.
f :: a ~ b => a -> b
f = id

-- | Write @foldMap@ for @HList@!
{--
foldMapH
  :: (Monoid m)
  => (a -> m)
  -> HList xs
  -> m
foldMapH _ HNil = mempty
foldMapH f (HCons a as) = f a <> (foldMapH f as)

Could not deduce: x ~ a
      from the context: xs ~ (x : xs1)<Paste>
-}
foldMapH
  :: (Monoid m, CAll ((~) a) xs)
  => (a -> m)
  -> HList xs
  -> m
foldMapH _ HNil = mempty
foldMapH f (HCons a as) = f a <> (foldMapH f as)
-- >>> xs = HCons (1 :: Int) (HCons (2 :: Int) (HCons (5 :: Int) HNil))
-- >>> foldMapH Sum xs
-- Sum 8
