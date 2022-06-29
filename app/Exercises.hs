module Exercises where

-- Exercise 1.4-i
e1 :: (b -> a) -> (c -> a) -> Either b c -> a
e1 f _ (Left b) = f b
e1 _ g (Right c) = g c

e2 :: (Either b c -> a) -> (b -> a, c -> a)
e2 f = (f . Left, f . Right)

-- Exercise 1.4-ii
f1 :: (c -> (a, b)) -> (c -> a, c -> b)
f1 f = (fst . f, snd . f)

f2 :: (c -> a) -> (c -> b) -> c -> (a, b)
f2 f g c = (f c, g c)

-- Exercise 1.4-ii
-- uncurry
g1 :: (c -> b -> a) -> (b, c) -> a
g1 f (b, c) = f c b

-- curry
g2 :: ((b, c) -> a) -> c -> b -> a
g2 f c b = f (b, c)
