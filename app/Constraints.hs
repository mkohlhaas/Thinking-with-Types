{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Constraints where

import Data.Kind (Constraint)

-- The CONSTRAINT kind is reserved for things that can appear on the left side of the fat context arrow (⇒).
-- This includes:
-- 1. Fully saturated typeclasses, e.g. `Show a`,
-- 2. Tuples of other constraints, e.g. `(Show a, Eq a)`
-- 3. Type equalities, e.g. `(Int ∼ a.)`

-- Both five and five_ are identical as far as Haskell is concerned.
-- While five has type Int, five_ has type a, along with a constraint saying that a equals Int.
five ∷ Int
five = 5

five_ ∷ (a ~ Int) ⇒ a
five_ = 5

type ShowAndNum a = (Show a, Num a)

-- # ShowNum
class (Show a, Num a) ⇒ ShowNum a

instance (Show a, Num a) ⇒ ShowNum a
