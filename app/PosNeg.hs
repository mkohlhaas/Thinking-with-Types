{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UnicodeSyntax #-}

module PosNeg where

---------------
-- Exercises --
---------------

-- Exercise 3-i

newtype T1 a = T1 (Int → a)

-- # FunctorT1
instance Functor T1 where
  fmap ∷ (a → b) → T1 a → T1 b
  -- fmap f (T1 a) = T1 $ fmap f a
  fmap f (T1 g) = T1 (f . g)

newtype T2 a = T2 (a → Int)

newtype T3 a = T3 (a → a)

newtype T4 a = T4 ((Int → a) → Int)

newtype T5 a = T5 ((a → Int) → Int)

-- # FunctorT5
instance Functor T5 where
  fmap ∷ (a → b) → T5 a → T5 b
  fmap f (T5 g) = T5 (\h → g (h . f))

-- If we can transform an `a` into a `b`, does that mean we can necessarily transform a `T a` into a `T b`?

-- 1. Covariant:     Any function a → b can be lifted into a function T a → T b.
-- 2. Contravariant: Any function a → b can be lifted into a function T b → T a.
-- 3. Invariant:     In general, functions a → b cannot be lifted into a function over T a.

-- A type T is a Functor if and only if it is covariant.

-- The variance of a type T a with respect to its type variable `a` is fully specified by whether `a` appears solely in
-- positive position, solely in negative position or in a mix of both.

-- Type variables which appear exclusively in POSITIVE position  are COVARIANT.
-- Type variables which appear exclusively in NEGATIVE position  are CONTRAVARIANT.
-- Type variables which appear             in BOTH     positions are INVARIANT.

-- Covariant variables (in POSITIVE position) are PRODUCED OR OWNED,
-- Contravariant variables (in NEGATIVE position) are CONSUMED.

class Contravariant f where
  contramap ∷ (a → b) → f b → f a

class Invariant f where
  invmap ∷ (a → b) → (b → a) → f a → f b

-- All types have a canonical representation expressed as some combination of `(,)`, `Either` and `(→)`.

--    Type     | Position of |
--             |  a   |  b   |
-- --------------------------|
-- Either a b  |  +   |  +   |
--   (a, b)    |  +   |  +   |
--   a → b     |  −   |  +   |

-- >>> :type words
-- words ∷ String → [String]

-- >>> :type show
-- show :: Show a => a -> String

-- >>> :type (words . show)
-- (words . show) :: Show a => a -> [String]

-- Variances behave like multiplication regarding to their signs:
-- | a | b | a ◦ b
-- | + | + |   +
-- | + | − |   −
-- | − | + |   −
-- | − | − |   +

-- T1: (Int -> a)        = a ⇒ covariant     (+)
-- T2: (a → Int)         = a ⇒ contravariant (-)
-- T3: (a → a)           = a ⇒ invariant     (±)
-- T4: ((Int → a) → Int) = a ⇒ contravariant (- × + = -)
-- T5: ((a → Int) → Int) = a ⇒ covariant     (- × - = +)

-- Only T1 and T5 are Functors.

-- A type that is covariant in two arguments (like Either and (,)) is called a BIFUNCTOR.
-- A type that is contravariant in its first argument, but covariant in its second (like (->)) is known as a PROFUNCTOR.

