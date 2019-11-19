{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
module Exercises where

import Data.Kind (Constraint, Type)
import Data.Function ((&))
import Data.Foldable (fold)


{- ONE -}

-- | One of the restrictions around classes that we occasionally hit is that we
-- can only have one instance for a type. There are, for example, two good
-- candidates for a monoid instance when we think about 'Integer':

data IntegerMonoid = Sum | Product

-- | a. Write a newtype around 'Integer' that lets us choose which instance we
-- want.
newtype Integer' (t :: IntegerMonoid) = Integer' { unInteger :: Integer }

-- | b. Write the two monoid instances for 'Integer'
-- Semigroup explicitly skipped
instance Monoid (Integer' 'Sum) where
  mempty = Integer' 0
  mappend (Integer' i) (Integer' i2) = Integer' (i + i2)

instance Monoid (Integer' Product) where
  mempty = Integer' 1
  mappend (Integer' i) (Integer' i2) = Integer' (i * i2)
-- >>> unInteger $ fold ([Integer' 2, Integer' 3] :: [Integer' 'Sum])
-- 5

-- | c. Why do we need @FlexibleInstances@ to do this?
-- Monoid (Integer' 'Sum) has a concret type and it's not supported by default.


{- TWO -}

-- | We can write a type that /is/ of kind 'Type', but has no value-level
-- members. We usually call this type 'Void':

data Void -- No constructors!

-- | a. If we promote this with DataKinds, can we produce any /types/ of kind
-- 'Void'?
-- No, because it has no data constructors to promote.

-- | b. What are the possible type-level values of kind 'Maybe Void'?
-- 'Nothing only. You can't instantiate 'Just because the kind Void has no promoted types.

-- | c. Considering 'Maybe Void', and similar examples of kinds such as
-- 'Either Void Bool', why do you think 'Void' might be a useful kind?
-- Indicates that a specific type choice does not exists.


{- THREE -}

-- | a. Write a GADT that holds strings or integers, and keeps track of how
-- many strings are present. Note that you might need more than 'Nil' and
-- 'Cons' this time...

data Nat = Z | S Nat

data StringAndIntList (stringCount :: Nat) (intCount :: Nat) where
  SCons :: String -> StringAndIntList n m -> StringAndIntList ('S n) m
  ICons :: Int    -> StringAndIntList n m -> StringAndIntList n ('S m)
  SNil  :: StringAndIntList 'Z 'Z

-- | b. Update it to keep track of the count of strings /and/ integers.

-- | c. What would be the type of the 'head' function?
siHead :: StringAndIntList n m -> Maybe (Either Int String)
siHead SNil = Nothing
siHead (SCons s _) = Just (Right s)
siHead (ICons i _) = Just (Left i)



{- FOUR -}

-- | When we talked about GADTs, we discussed existentials, and how we could
-- only know something about our value if the context told us:

data Showable where
  Showable :: Show a => a -> Showable

-- | a. Write a GADT that holds something that may or may not be showable, and
-- stores this fact in the type-level.

data MaybeShowable (isShowable :: Bool) where
  JustShowable :: (Show a) => a -> MaybeShowable 'True
  NothingShowable :: a -> MaybeShowable 'False

-- | b. Write a 'Show' instance for 'MaybeShowable'. Your instance should not
-- work unless the type is actually 'show'able.
instance Show (MaybeShowable 'True) where
  show (JustShowable a) = show a
-- >>> show $ JustShowable "UwU"
-- >>> show $ NothingShowable "O.O" -- Fails to compile

-- | c. What if we wanted to generalise this to @Constrainable@, such that it
-- would work for any user-supplied constraint of kind 'Constraint'? How would
-- the type change? What would the constructor look like? Try to build this
-- type - GHC should tell you exactly which extension you're missing.
--   -XConstraintKinds: https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#extension-ConstraintKinds
data Constrainable (c :: Type -> Constraint) (isShowable :: Bool) where
  HasConstraint :: (c a) => a -> Constrainable c 'True
  HasntConstraint :: a -> Constrainable c 'False


{- FIVE -}

-- | Recall our list type:

data List a = Nil | Cons a (List a)

-- | a. Use this to write a better 'HList' type than we had in the @GADTs@
-- exercise. Bear in mind that, at the type-level, 'Nil' and 'Cons' should be
-- "ticked". Remember also that, at the type-level, there's nothing weird about
-- having a list of types!

data HList (types :: [ts]) where
   HNil  :: HList '[]
   HCons :: t -> HList ts -> HList (t ': ts)

-- | b. Write a well-typed, 'Maybe'-less implementation for the 'tail' function
-- on 'HList'.
htail :: HList (t ': ts) -> HList ts
htail (HCons _ ts) = ts

-- | c. Could we write the 'take' function? What would its type be? What would
-- get in our way?
--
-- take :: Int -> HList ts -> HList (Take ts)
-- We need a type-level function to compute the type of Take Int ts
-- fcf ;)

{- SIX -}

-- | Here's a boring data type:

{-
data BlogAction
  = AddBlog
  | DeleteBlog
  | AddComment
  | DeleteComment
-}

-- | a. Two of these actions, 'DeleteBlog' and 'DeleteComment', should be
-- admin-only. Extend the 'BlogAction' type (perhaps with a GADT...) to
-- express, at the type-level, whether the value is an admin-only operation.
-- Remember that, by switching on @DataKinds@, we have access to a promoted
-- version of 'Bool'!

data BlogAction (isAdmin :: Bool) where
  AddBlog       :: BlogAction 'False
  DeleteBlog    :: BlogAction 'True
  AddComment    :: BlogAction 'False
  DeleteComment :: BlogAction 'True

-- | b. Write a 'BlogAction' list type that requires all its members to be
-- the same "access level": "admin" or "non-admin".

newtype BlogActionList = BlogActionList [BlogAction 'True]

-- | c. Let's imagine that our requirements change, and 'DeleteComment' is now
-- available to a third role: moderators. Could we use 'DataKinds' to introduce
-- the three roles at the type-level, and modify our type to keep track of
-- this?

data Role
  = User
  | Admin
  | Moderator

data BlogAction' (r :: Role) where -- role is not acceptable
  AddBlog'       :: BlogAction' 'User
  DeleteBlog'    :: BlogAction' 'Admin
  AddComment'    :: BlogAction' 'User
  DeleteComment' :: BlogAction' 'Moderator


{- SEVEN -}

-- | When we start thinking about type-level Haskell, we inevitably end up
-- thinking about /singletons/. Singleton types have a one-to-one value-type
-- correspondence - only one value for each type, only one type for each value.
-- A simple example is '()', whose only value is '()'. 'Bool' is /not/ a
-- singleton, because it has multiple values.

-- We can, however, /build/ a singleton type for 'Bool':

data SBool (value :: Bool) where
  SFalse :: SBool 'False
  STrue  :: SBool 'True

-- | a. Write a singleton type for natural numbers:

data SNat (value :: Nat) where
  SZ :: SNat 'Z
  SN :: SNat n -> SNat ('S n)

-- | b. Write a function that extracts a vector's length at the type level:
vlength :: Vector n a -> SNat n
vlength VNil        = SZ
vlength (VCons _ v) = SN (vlength v)

-- | c. Is 'Proxy' a singleton type?

data Proxy a = Proxy
-- It's not. Proxy :: Proxy Int and Proxy :: Proxy String have more than one type for each value.





{- EIGHT -}

-- | Let's imagine we're writing some Industry Haskell™, and we need to read
-- and write to a file. To do this, we might write a data type to express our
-- intentions:


data Program                     result
  = OpenFile            (Program result)
  | WriteFile  String   (Program result)
  | ReadFile  (String -> Program result)
  | CloseFile (          Program result)
  | Exit                         result


-- | We could then write a program like this to use our language:

myApp :: Program Bool
myApp
  = OpenFile $ WriteFile "HEY" $ (ReadFile $ \contents ->
      if contents == "WHAT"
        then WriteFile "... bug?" $ Exit False
        else CloseFile            $ Exit True)

-- | ... but wait, there's a bug! If the contents of the file equal "WHAT", we
-- forget to close the file! Ideally, we would like the compiler to help us: we
-- could keep track of whether the file is open at the type level!
--
-- - We should /not/ be allowed to open a file if another file is currently
-- open.
--
-- - We should /not/ be allowed to close a file unless a file is open.
--
-- If we had this at the type level, the compiler should have been able to tell
-- us that the branches of the @if@ have different types, and this program
-- should never have made it into production. We should also have to say in the
-- type of 'myApp' that, once the program has completed, the file will be
-- closed.

-- | Improve the 'Program' type to keep track of whether a file is open.  Make
-- sure the constructors respect this flag: we shouldn't be able to read or
-- write to the file unless it's open. This exercise is a bit brain-bending;
-- why? How could we make it more intuitive to write?

-- On thinking-with-types there's a better way of keeping track of open files.
data Program' (isFileOpen :: Bool) (result :: Type) where
  OpenFile'  :: Program' 'True result             -> Program' 'False result
  WriteFile' :: String -> Program' 'True result   -> Program' 'True result
  ReadFile'  :: (String -> Program' 'True result) -> Program' 'True result
  CloseFile' :: Program' 'False result            -> Program' 'True result
  Exit'      :: result                            -> Program' 'False result

mySaveApp :: Program' 'False Bool
mySaveApp = OpenFile' $ WriteFile' "HEY" $
              ReadFile' $ \contents ->
                if contents == "WHAT"
                  then WriteFile' "... bug?" $ CloseFile' $ Exit' False
                  else CloseFile' $ Exit' True

-- Code that leaks resources won't compile
--mySaveApp2 :: Program' 'False Bool
--mySaveApp2 = OpenFile' $ ReadFile' (\contents -> CloseFile' $ WriteFile' "... bug?" $ CloseFile' $ Exit' False)

-- | EXTRA: write an interpreter for this program. Nothing to do with data
-- kinds, but a nice little problem.

interpret :: Program' any a -> IO a
interpret (OpenFile' k)             = putStrLn "Opening file." >> interpret k
interpret (WriteFile' newContent k) = putStrLn ("Writing " ++ newContent ++ " to the file...") >> interpret k
interpret (ReadFile' k)             = putStrLn "Reading file." >> interpret (k "Some content")
interpret (CloseFile' k)            = putStrLn "Closing file." >> interpret k
interpret (Exit' result)            = putStrLn "Closing app." >> return result

data Program'' (openFiles :: Nat) (result :: Type) where
  OpenFile''  :: Program'' (S n) result              -> Program'' n result
  WriteFile'' :: String -> Program'' (S n) result    -> Program'' (S n) result
  ReadFile''  :: (String -> Program'' (S n) result)  -> Program'' (S n) result
  CloseFile'' :: Program'' n result                  -> Program'' (S n) result
  Exit''      :: result                              -> Program'' Z result

mySaveApp2 :: Program'' Z Bool
mySaveApp2
  = OpenFile'' $
      ReadFile'' $ \contents ->
        if (null contents)
          then WriteFile'' "New content" $ CloseFile'' $ Exit'' True
          -- won't compile, nice!
          --else OpenFile'' $ CloseFile'' $ Exit'' False
          else OpenFile'' $ CloseFile'' $ CloseFile'' $ Exit'' False

{- NINE -}

-- | Recall our vector type:

data Vector (n :: Nat) (a :: Type) where
  VNil  :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | Imagine we want to write the '(!!)' function for this vector. If we wanted
-- to make this type-safe, and avoid 'Maybe', we'd have to have a type that can
-- only hold numbers /smaller/ than some type-level value.

-- | a. Implement this type! This might seem scary at first, but break it down
-- into Z and S cases. That's all the hint you need :)

data SmallerThan (limit :: Nat) where
  -- Z is smaller than the successor of any number.
  SmallerThanZ :: SmallerThan ('S n)
  -- The successor of a number smaller than X is a number smaller than the
  -- successor of X.
  SmallerThanS :: SmallerThan n -> SmallerThan ('S n)

-- | b. Write the '(!!)' function:

(!!) :: Vector n a -> SmallerThan n -> a
(!!) (VCons a _) SmallerThanZ     = a
(!!) (VCons _ xs) (SmallerThanS n) = xs Exercises.!! n

-- | c. Write a function that converts a @SmallerThan n@ into a 'Nat'.
smallerThanToNat :: SmallerThan n -> Nat
smallerThanToNat SmallerThanZ     = Z
smallerThanToNat (SmallerThanS n) = S (smallerThanToNat n)
