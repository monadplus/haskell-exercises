{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE UndecidableInstances #-}
module Exercises where

import Data.Foldable (fold)
import Data.Monoid
import Data.Typeable (Typeable, cast)
import Text.Printf (printf)

{- ONE -}

-- | Let's introduce a new class, 'Countable', and some instances to match.
class Countable a where
  count :: a -> Int

instance Countable Int  where count   = id
instance Countable [a]  where count   = length
instance Countable Bool where count x = if x then 1 else 0

-- | a. Build a GADT, 'CountableList', that can hold a list of 'Countable'
-- things.

data CountableList where
  CNil  :: CountableList
  CCons :: (Typeable a, Countable a) => a -> CountableList -> CountableList

-- | b. Write a function that takes the sum of all members of a 'CountableList'
-- once they have been 'count'ed.

countList :: CountableList -> Int
countList CNil = 0
countList (CCons a clist) = count a + countList clist


-- | c. Write a function that removes all elements whose count is 0.

dropZero :: CountableList -> CountableList
dropZero CNil = CNil
dropZero (CCons a clist)
  | count a == 0 = dropZero clist
  | otherwise = CCons a (dropZero clist)


-- | d. Can we write a function that removes all the things in the list of type
-- 'Int'? If not, why not?
--   * Only if we add a Typeablee constraint.

filterInts :: CountableList -> CountableList
filterInts CNil = CNil
filterInts (CCons a clist)
  | Just _ <- cast @_ @Int a = filterInts clist
  | otherwise = CCons a (filterInts clist)


{- TWO -}

-- | a. Write a list that can take /any/ type, without any constraints.

data AnyList where
  ANil :: AnyList
  ACons ::  a -> AnyList -> AnyList

-- | b. How many of the following functions can we implement for an 'AnyList'?

reverseAnyList :: AnyList -> AnyList
reverseAnyList = go ANil
  where
    go acc ANil = acc
    go acc (ACons a alist) = go (ACons a acc) alist

-- This one can't be implemented as the a of AnyList is different from the a of the signature.
--filterAnyList :: (a -> Bool) -> AnyList -> AnyList

-- This is not useful.
filterAnyList :: (forall a. a -> Bool) -> AnyList -> AnyList
filterAnyList _ ANil = ANil
filterAnyList p (ACons a alist)
  | p a = filterAnyList p alist
  | otherwise = ACons a (filterAnyList p alist)


lengthAnyList :: AnyList -> Int
lengthAnyList ANil = 0
lengthAnyList (ACons _ alist) = 1 + lengthAnyList alist

-- Not useful.
foldAnyList :: Monoid m => AnyList -> m
foldAnyList _ = mempty

isEmptyAnyList :: AnyList -> Bool
isEmptyAnyList alist
  | ANil <- alist = True
  | otherwise     = False

-- Content can't be enumerated.
instance Show AnyList where
  show = const "What about us ?" -- error "What about me?"





{- THREE -}

-- | Consider the following GADT:

data TransformableTo output where
  TransformWith
    :: (input -> output)
    ->  input
    -> TransformableTo output

-- | ... and the following values of this GADT:

transformable1 :: TransformableTo String
transformable1 = TransformWith show 2.5

transformable2 :: TransformableTo String
transformable2 = TransformWith (uncurry (++)) ("Hello,", " world!")

-- | a. Which type variable is existential inside 'TransformableTo'? What is
-- the only thing we can do to it? Apply f

-- | b. Could we write an 'Eq' instance for 'TransformableTo'? What would we be
-- able to check? The output :P

instance Eq output => Eq (TransformableTo output) where
  (TransformWith f i) == (TransformWith f2 i2) = f i == f2 i2

-- | c. Could we write a 'Functor' instance for 'TransformableTo'? If so, write
-- it. If not, why not?
instance Functor TransformableTo where
  fmap g (TransformWith f i) = TransformWith (g . f) i


{- FOUR -}

-- | Here's another GADT:

data EqPair where
  EqPair :: Eq a => a -> a -> EqPair

-- | a. There's one (maybe two) useful function to write for 'EqPair'; what is
-- it?
isEqual :: EqPair -> Bool
isEqual (EqPair a a1) = a == a1
-- Couldn't match expected type ‘a’ with actual type ‘a1’
--areEqual :: EqPair -> EqPair -> Bool
--areEqual (EqPair a a1) (EqPair b b1) = a == b && a1 == b1

-- | b. How could we change the type so that @a@ is not existential? (Don't
-- overthink it!)
data EqPair' a where
  EqPair' :: Eq a => a -> a -> EqPair' a

-- | c. If we made the change that was suggested in (b), would we still need a
-- GADT? Or could we now represent our type as an ADT?
data EqPair'' a = EqPair'' a a -- You lost the information about Equality




{- FIVE -}

-- | Perhaps a slightly less intuitive feature of GADTs is that we can set our
-- type parameters (in this case @a@) to different types depending on the
-- constructor.

data MysteryBox a where
  EmptyBox  ::                                MysteryBox ()
  IntBox    :: Int    -> MysteryBox ()     -> MysteryBox Int
  StringBox :: String -> MysteryBox Int    -> MysteryBox String
  BoolBox   :: Bool   -> MysteryBox String -> MysteryBox Bool

-- | When we pattern-match, the type-checker is clever enough to
-- restrict the branches we have to check to the ones that could produce
-- something of the given type.

getInt :: MysteryBox Int -> Int
getInt (IntBox int _) = int

-- | a. Implement the following function by returning a value directly from a
-- pattern-match:

getInt' :: MysteryBox String -> Int
getInt' (StringBox _ mbI) = getInt mbI

-- | b. Write the following function. Again, don't overthink it!

countLayers :: MysteryBox a -> Int
countLayers EmptyBox         = 1
countLayers (IntBox    _ mb) = 1 + countLayers mb
countLayers (StringBox _ mb) = 1 + countLayers mb
countLayers (BoolBox   _ mb) = 1 + countLayers mb

-- | c. Try to implement a function that removes one layer of "Box". For
-- example, this should turn a BoolBox into a StringBox, and so on. What gets
-- in our way? What would its type be?
removeLayer :: MysteryBox a -> MysteryBox b
removeLayer = error "Can't be implemented this way because of typee equality"
--removeLayer EmptyBox         = (EmptyBox :: MysteryBox b)
--removeLayer (IntBox    _ mb) = mb -- Could not deduce: b ~ () from the context: a ~ Int
--removeLayer (StringBox _ mb) = 1 + countLayers mb
--removeLayer (BoolBox   _ mb) = 1 + countLayers mb




{- SIX -}

-- | We can even use our type parameters to keep track of the types inside an
-- 'HList'!  For example, this heterogeneous list contains no existentials:

data HList a where
  HNil  :: HList ()
  HCons :: head -> HList tail -> HList (head, tail) -- Because typelevel lists are too mainstream.
--data HList (ts :: [Type]) where
  --HNil :: HList '[]
  --(:#) :: t -> HList ts -> HList (t ': ts)
--infixr 5 :#

exampleHList :: HList (String, (Int, (Bool, ())))
exampleHList = HCons "Tom" (HCons 25 (HCons True HNil))

-- | a. Write a 'head' function for this 'HList' type. This head function
-- should be /safe/: you can use the type signature to tell GHC that you won't
-- need to pattern-match on HNil, and therefore the return type shouldn't be
-- wrapped in a 'Maybe'!
headHList :: HList (h, t) -> h
headHList (HCons h t) = h

-- | b. Currently, the tuples are nested. Can you pattern-match on something of
-- type @HList (Int, String, Bool, ())@? Which constructor would work?

patternMatchMe :: HList (Int, String, Bool, ()) -> Int
patternMatchMe = error "Not like this"

patternMatchMe' :: HList (Int, b) -> Int
patternMatchMe' (HCons h t) = h

-- | c. Can you write a function that appends one 'HList' to the end of
-- another? What problems do you run into?

--appendHList :: HList a -> HList b -> HList (a,b)
--appendHList ((HCons h HNil)::HList (a, ())) b = HCons h b -- Couldn't match type ‘a1’ with ‘(a, ())’
appendHList :: HList (a, ()) -> HList b -> HList (a,b)
appendHList (HCons h _) b = HCons h b



{- SEVEN -}

-- | Here are two data types that may help:

data Empty
data Branch left centre right

-- | a. Using these, and the outline for 'HList' above, build a heterogeneous
-- /tree/. None of the variables should be existential.

data HTree a where
  HLeaf :: HTree Empty
  HBranch :: HTree left -> center -> HTree right -> HTree (Branch left center right)
  -- ...

-- | b. Implement a function that deletes the left subtree. The type should be
-- strong enough that GHC will do most of the work for you. Once you have it,
-- try breaking the implementation - does it type-check? If not, why not?
pruneLeft :: HTree (Branch left center right) -> HTree (Branch Empty center right)
pruneLeft (HBranch _ center right) = HBranch  HLeaf center right
-- >>> htree = HBranch (HBranch HLeaf "left branch" HLeaf) "centre" (HBranch HLeaf "right branch" HLeaf)
-- >>> pruneLeft htree

-- | c. Implement 'Eq' for 'HTree's. Note that you might have to write more
-- than one to cover all possible HTrees. You might also need an extension or
-- two, so look out for something... flexible... in the error messages!
-- Recursion is your friend here - you shouldn't need to add a constraint to
-- the GADT!

-- Requires -XFlexibleInstances and -XFlexibleContexts
instance Eq (HTree Empty)
  where _ == _ = True

instance (Eq (HTree left), Eq centre, Eq (HTree right)) => Eq (HTree (Branch left centre right)) where
  HBranch l x r == HBranch l' x' r' = l == l' && x == x' && r == r'

-- Same for show
instance Show (HTree Empty)
  where show _ = "."

instance (Show (HTree left), Show centre, Show (HTree right)) => Show (HTree (Branch left centre right)) where
  show (HBranch left centre right) = "L ( " ++ show left ++ " ) [" ++ show centre ++ "] R ( " ++ show right ++ ")"
  -- It's a bit more involved because you can't use an HTree a.
  --show = showAtLevel 0
    --where
    --addSpace = flip replicate '\t'
    --showAtLevel :: Int -> HTree a -> String
    --showAtLevel l HLeaf                      = addSpace l ++ "*"
    --showAtLevel l (HBranch lt x rt) = printf "%s%s\n%s\n%s" (addSpace l) (show x) (showAtLevel (l + 1) lt) (showAtLevel (l + 1) rt)

{- EIGHT -}

-- | a. Implement the following GADT such that values of this type are lists of
-- values alternating between the two types. For example:
--
-- @
--   f :: AlternatingList Bool Int
--   f = ACons True (ACons 1 (ACons False (ACons 2 ANil)))
-- @

data AlternatingList a b where
  ALNil :: AlternatingList a b
  ALCons :: a -> AlternatingList b a -> AlternatingList a b


getFirsts :: AlternatingList a b -> [a]
getFirsts ALNil = []
getFirsts (ALCons a abs) = a : (getSeconds abs)
-- >>> xs = ALCons (All True) (ALCons (Sum 1) (ALCons (All False) (ALCons (Sum 2) ALNil))); xs :: AlternatingList All (Sum Int)
-- >>> getFirsts xs
-- [True,False]

getSeconds :: AlternatingList a b -> [b]
getSeconds ALNil = []
getSeconds (ALCons _ abs) = getFirsts abs
-- >>> getSeconds xs
-- [1,2]

-- | c. One more for luck: write this one using the above two functions, and
-- then write it such that it only does a single pass over the list.

foldValues :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues ablist =
  (fold (getFirsts ablist), fold (getSeconds ablist))
-- >>> foldValues xs
-- (All {getAll = False},Sum {getSum = 3})

foldValues' :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues' ALNil = (mempty, mempty)
foldValues' (ALCons a abs) = let (b, a') = foldValues' abs in (a `mappend` a', b)


{- NINE -}

-- | Here's the "classic" example of a GADT, in which we build a simple
-- expression language. Note that we use the type parameter to make sure that
-- our expression is well-formed.

data Expr a where
  Equals    :: Expr Int  -> Expr Int            -> Expr Bool
  Add       :: Expr Int  -> Expr Int            -> Expr Int
  If        :: Expr Bool -> Expr a   -> Expr a  -> Expr a
  IntValue  :: Int                              -> Expr Int
  BoolValue :: Bool                             -> Expr Bool

-- | a. Implement the following function and marvel at the typechecker:

eval :: Expr a -> a
eval (Equals e1 e2) = eval(e1) == eval(e2)
eval (Add e1 e2)    = eval(e1) + eval(e2)
eval (If p e1 e2)   = if eval(p) then eval(e1) else eval(e2)
eval (IntValue i)   = i
eval (BoolValue b)  = b
-- >>> eval $ If (BoolValue True) (Add (IntValue 2)(IntValue 3)) (IntValue 0)
-- 5


-- | b. Here's an "untyped" expression language. Implement a parser from this
-- into our well-typed language. Note that (until we cover higher-rank
-- polymorphism) we have to fix the return type. Why do you think this is?

data DirtyExpr
  = DirtyEquals    DirtyExpr DirtyExpr
  | DirtyAdd       DirtyExpr DirtyExpr
  | DirtyIf        DirtyExpr DirtyExpr DirtyExpr
  | DirtyIntValue  Int
  | DirtyBoolValue Bool

-- This is a super tricky one. First, we need a GADT that means we can
-- patten-match to figure out the type of our expression. If we have an
-- @IntType x@, we know that @x :: Expr Int@. Similarly for @BoolType x@!

data Typed where
  IntType  :: Expr Int  -> Typed
  BoolType :: Expr Bool -> Typed

-- Now, we do some really grotty pattern-matching to guarantee that our types
-- line up. 'Typed' gives us a way to figure out whether we have the right
-- types, and so we can just start to put together an expression. The nice
-- thing here is that it's pretty much guaranteed to work if it compiles
-- because of how strict the types are!
tidy :: DirtyExpr -> Maybe Typed

tidy (DirtyEquals x y) = case (tidy x, tidy y) of
  (Just (IntType e1), Just (IntType e2)) -> Just (BoolType (Equals e1 e2))
  _                                      -> Nothing


tidy (DirtyAdd x y) = case (tidy x, tidy y) of
  (Just (IntType e1), Just (IntType e2)) -> Just (IntType (Add e1 e2))
  _                                      -> Nothing

tidy (DirtyIf p x y) = case (tidy p, tidy x, tidy y) of
  (Just (BoolType b), Just (BoolType e1), Just (BoolType e2)) -> Just (BoolType (If b e1 e2))
  (Just (BoolType b), Just (IntType e1),  Just (IntType e2))  -> Just (IntType (If b e1 e2))
  _                                                           -> Nothing

tidy (DirtyIntValue i) = Just (IntType (IntValue i))
tidy (DirtyBoolValue b) = Just (BoolType (BoolValue b))

parse :: DirtyExpr -> Maybe (Expr Int)
parse de = case tidy de of
  Just (IntType i) ->  Just i
  _                -> Nothing
-- >>> eval <$> (parse $ DirtyAdd (DirtyIf (DirtyBoolValue True) (DirtyIntValue 2) (DirtyIntValue 3)) (DirtyIntValue 8))
-- Just 10
-- >>> eval <$> (parse $ DirtyAdd (DirtyIf (DirtyIntValue 0) (DirtyIntValue 2) (DirtyIntValue 3)) (DirtyIntValue 8))
-- Nothing

-- | c. Can we add functions to our 'Expr' language? If not, why not? What
-- other constructs would we need to add? Could we still avoid 'Maybe' in the
-- 'eval' function?

-- Lambda Calculus
-- (λx.x)(λy.y)
--     |        Var
-- |----|       Lam
-- |----------| App
type Name = String

data Exp
  = Var' Name
  | Lam' Name Exp
  | App' Exp Exp


--Higher Order Abstract Syntax (HOAS) is a technique for implementing the lambda calculus in a language where the binders of the lambda expression map directly onto lambda binders of the host language ( i.e. Haskell ) to give us substitution machinery in our custom language by exploiting Haskell's implementation.

data Expr' a where
  Equals'    :: Expr' Int  -> Expr' Int            -> Expr' Bool
  Add'       :: Expr' Int  -> Expr' Int            -> Expr' Int
  If'        :: Expr' Bool -> Expr' a   -> Expr' a -> Expr' a
  IntValue'  :: Int                                -> Expr' Int
  BoolValue' :: Bool                               -> Expr' Bool
  App        :: Expr' (a -> b) -> Expr' a          -> Expr' b
  -- We need a way to lift a function into our Expr' language
  Lam        :: (a -> Expr' b) -> Expr' (a -> b)
  -- This is an alternative implementation.
  --Con :: a -> Expr a
  --Lam :: (Expr a -> Expr b) -> Expr (a -> b)
  --App :: Expr (a -> b) -> Expr a -> Expr b

eval' :: Expr' a -> a
eval' (Equals' e1 e2) = eval'(e1) == eval'(e2)
eval' (Add' e1 e2)    = eval'(e1) + eval'(e2)
eval' (If' p e1 e2)   = if eval'(p) then eval'(e1) else eval'(e2)
eval' (IntValue' i)   = i
eval' (BoolValue' b)  = b
eval' (Lam f)         = \a -> eval' (f a)
eval' (App f a)       = eval' f (eval' a)
-- >>> isZero  = Lam  $ \i -> BoolValue' (i == 0)
-- >>> eval' $ App isZero (IntValue' 0)
-- >>> eval' $ App isZero (IntValue' 10)
-- >>> eval' $ App (Lam $ \v -> let v' = IntValue' v in If' (App isZero v') (Add' v' (IntValue' 5)) v') (IntValue' 0)



{- TEN -}

-- | Back in the glory days when I wrote JavaScript, I could make a composition
-- list like @pipe([f, g, h, i, j])@, and it would pass a value from the left
-- side of the list to the right. In Haskell, I can't do that, because the
-- functions all have to have the same type :(

-- | a. Fix that for me - write a list that allows me to hold any functions as
-- long as the input of one lines up with the output of the next.

data TypeAlignedList a b where
  TALNil :: TypeAlignedList a a
  -- nb. a b are not the same as below
  TALCons :: (a -> b) -> TypeAlignedList b c -> TypeAlignedList a c

-- | b. Which types are existential?
-- The intermediate types, only a anb c and know at compile type.

-- | c. Write a function to append type-aligned lists. This is almost certainly
-- not as difficult as you'd initially think.

-- hint: think about what you need to solve this equation.
-- TypeAlignedList a c :: (a -> x) and TypeAlignedList x c
-- (a -> x) can only be found in the first parameter of the second argument!
-- TypeAlignedList x c can't be found in the wild but we have:
--   ys :: TypeAlignedList x b
--   xs :: TypeAlignedList b c
-- So we only need a way of compose both TypeAlignedList ... wait... composeTALs is the answer!
composeTALs :: TypeAlignedList b c -> TypeAlignedList a b -> TypeAlignedList a c
composeTALs xs TALNil = xs -- b ~ a then xs :: TypeAlignedList a c
composeTALs xs (TALCons f ys) = TALCons f (composeTALs xs ys)

evalTAL :: TypeAlignedList a b -> (a -> b)
evalTAL TALNil = id
evalTAL (TALCons f xs) = (evalTAL xs) . f

-- >>> talf = TALCons show TALNil; talf :: TypeAlignedList (Maybe Int) String
-- >>> talg = TALCons (++ "!") TALNil
-- >>> (evalTAL $ composeTALs talg talf) (Just 7)
