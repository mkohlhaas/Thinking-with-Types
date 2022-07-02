{-# LANGUAGE DataKinds, TypeFamilies, UnicodeSyntax #-}

module Exercises where

-- Exercise 1.4-i
e1 ∷ (b → a) → (c → a) → Either b c → a
e1 f _ (Left b)  = f b
e1 _ g (Right c) = g c

e2 ∷ (Either b c → a) → (b → a, c → a)
e2 f = (f . Left, f . Right)

-- Exercise 1.4-ii
f1 ∷ (c → (a, b)) → (c → a, c → b)
f1 f = (fst . f, snd . f)

f2 ∷ (c → a) → (c → b) → c → (a, b)
f2 f g c = (f c, g c)

-- Exercise 1.4-ii
-- "uncurry" (https://github.com/isovector/thinking-with-types/issues/28)
g1 ∷ (c → b → a) → (b, c) → a
g1 f (b, c) = f c b

-- "curry"
g2 ∷ ((b, c) → a) → c → b → a
g2 f c b = f (b, c)

-- Exercise 2.1.3-i
-- ghci> :k Show
-- Show :: Type -> Constraint

-- Exercise 2.1.3-ii
-- ghci> :k Functor
-- Functor :: (Type -> Type) -> Constraint

-- Exercise 2.1.3-iii
-- ghci> :k Monad
-- Monad :: (Type -> Type) -> Constraint

-- Exercise 2.1.3-iv
-- ghci> import Control.Monad.Trans
-- ghci> :k MonadTrans
-- MonadTrans :: ((Type -> Type) -> Type -> Type) -> Constraint

-- Exercise 2.1.4-i
type family Not (x :: Bool) :: Bool where
  Not 'True = 'False
  Not 'False = 'True

-- Exercise 3-i
newtype T1 a = T1 (Int → a) -- covariant

newtype T2 a = T2 (a → Int) -- contravariant

newtype T3 a = T3 (a → a) -- invariant (co- and contravariant)

newtype T4 a = T4 ((Int → a) → Int) -- contravariant

newtype T5 a = T5 ((a → Int) → Int) -- covariant

instance Functor T1 where
  fmap f (T1 a) = T1 $ f . a

-- fmap for functions is compose (.)
-- fmap f (T1 a) = T1 $ f <$> a

instance Functor T5 where
  fmap f (T5 g) = T5 $ \h -> g $ h . f

-- 'Quasi-Pattern-matching' of functions via lambda.
-- h :: b -> Int
-- f :: a -> b
-- h . f :: a -> Int
-- g :: (a -> Int) -> Int

-- fmap for functions is compose (.)
-- fmap f (T5 g) = T5 $ \bi -> g $ bi <$> f
