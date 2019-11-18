module Exercises where

class PopQuiz a

-- | Which of the following instances require 'FlexibleInstances'? Don't cheat
-- :D This is a tricky one, but look out for nested concrete types!

instance PopQuiz Bool
--instance PopQuiz [Bool] -- This
instance PopQuiz [a]
instance PopQuiz (a, b)
--instance PopQuiz [(a, b)] -- This
instance PopQuiz (IO a)

newtype RIO  r a = RIO (r -> IO a) -- Remember, this is a /new type/.
type    RIO' r a =      r -> IO a

--instance PopQuiz (RIO Int a) -- This because of Int
instance PopQuiz (RIO r a)
--instance PopQuiz (RIO' r a) -- This because of type synonym
--instance PopQuiz (r -> IO a) -- ((->) r (IO a))  -- This because of IO a
instance PopQuiz (a -> b) -- ((->) a b).
--instance PopQuiz (a -> b -> c) -- ((->) a ((->) b c)) -- This becaue of b -> c
instance PopQuiz (a, b, c)
--instance PopQuiz (a, (b, c)) -- This because of (b, c)
instance PopQuiz ()
--instance PopQuiz (a, b, c, a) -- This because of repeated a

data Pair  a = Pair  a  a
type Pair' a =      (a, a)

--instance PopQuiz (a, a) -- This
instance PopQuiz (Pair a)
--instance PopQuiz (Pair' a) -- This
