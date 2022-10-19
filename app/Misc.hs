{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module Misc where

import GHC.TypeLits

-- # showFunc
instance
  ( TypeError
      ( 'Text "Attempting to interpret a number as a function "
          ':$$: 'Text "in the type `"
            ':<>: 'ShowType (a → b)
            ':<>: 'Text "'"
          ':$$: 'Text "Did you forget to specify the function you wanted?"
      )
  ) ⇒
  Num (a → b)

-- Behavour depends on ScopedTypeVariables.
broken ∷ (a → b) → a → b
broken f a = apply
  where
    -- apply ∷ b -- this is a different `b`
    apply = f a

-- The `∀ a b` quantifier introduces a type scope and exposes the type variables `a` and `b` to the remainder of the function.
-- This allows us to reuse `b` when adding the type signature to apply, rather than introducing a new type variable.
working ∷ ∀ a b. (a → b) → a → b
working f a = apply
  where
    apply ∷ b -- same `b`
    apply = f a

-- # Refl
data a :~: b where
  Refl ∷ a :~: a

data Proxy a = Proxy

{-

data Maybe a
  = Just a
  | Nothing

-}

-- >>> :type fmap
-- fmap ∷ Functor f ⇒ (a → b) → f a → f b

-- Functor f is now Maybe
-- >>> :set -XTypeApplications
-- >>> :type fmap @Maybe
-- fmap @Maybe ∷ (a → b) → Maybe a → Maybe b

-- We've applied the type Maybe to the polymorphic function fmap in the same way we can apply value arguments to functions.

-- Two rules:
-- 1. Types are applied in the same order they appear in a type signature - including its context and ∀ quantifiers!
--    Type applying Int to `a → b → a`        results in `Int → b → Int`.
--    Type applying Int to `∀ b a. a → b → a` results in `a → Int → a`.
-- 2. We can avoid applying a type with an underscore: `@_`.
--    This means we can also specialize type variables which are not the first in line.

-- >>> :t fmap
-- fmap ∷ Functor f ⇒ (a → b) → f a → f b

-- >>> :set -XTypeApplications
-- >>> :t fmap @_ @Int @Bool
-- fmap @_ @Int @Bool ∷ Functor w ⇒ (Int → Bool) → w Int → w Bool

-- Pay attention to type order whenever you write a function that might be type applied.
-- As a guiding principle, the hardest types to infer must come first.
