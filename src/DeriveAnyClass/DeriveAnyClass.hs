{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

--------------------------
-- Chapter 13: Generics --
--------------------------

-- 13.1 Generic Representations
-- 13.2 Deriving Structural Polymorphism
-- 13.3 Using Generic Metadata
-- 13.4 Performance
-- 13.5 Kan Extensions

module DeriveAnyClass where

import GHC.Generics

-- Two types of polymorphism: parametric and ad-hoc polymorphism.

-- PARAMETRIC POLYMORPHISM gives one definition for every possible type (think head ∷ [a] → a.)
-- It's what you get when you write a standard Haskell function with type variables.
-- This flavor of polymorphism is predictable.
-- The same function must always do the same thing, regardless of the types it's called with.

-- AD-HOC POLYMORPHISM allows us to write a different implementation for every type as made possible by typeclasses.

-- Third type: STRUCTURAL POLYMORPHISM.
-- Structural polymorphism doesn't have any formal definition.
-- It's the sort of thing you recognize when you see it.
-- Structural polymorphism is ad-hoc in the sense of being different for each type, but it is also highly regular and predictable.
-- It's what's colloquially known as "boilerplate". e.g. Eq, Show and Functor instances.

-- Foo
data Foo a b c = F0 | F1 !a | F2 !b !c
  deriving (Generic, MyEq)

-- Eq typeclass implementations are always of the following form:

-- instance (Eq a, Eq b, Eq c) ⇒ Eq (Foo a b c) where
--   (==) ∷ (Eq a, Eq b, Eq c) ⇒ Foo a b c → Foo a b c → Bool
--   F0 == F0 = True
--   F1 a1 == F1 a2 = a1 == a2
--   F2 b1 c1 == F2 b2 c2 = b1 == b2 && c1 == c2
--   _ == _ = False

-- Writing this instance is just mechanic. We can do this using Generics!

----------------------------------
-- 13.1 Generic Representations --
----------------------------------

-- All types have a canonical representation as a sum-of-products.
-- Sum-of-Products ≅ Eithers of pairs.

-- >>> toCanonical Nothing
-- Left ()

-- >>> toCanonical (Just "hello")
-- Right "hello"

-- >>> fromCanonical (Left ())
-- Nothing

-- >>> fromCanonical (Right "hello")
-- Just "hello"

-- >>> :type fromCanonical . toCanonical
-- fromCanonical . toCanonical ∷ Maybe a → Maybe a

-- >>> :type toCanonical . fromCanonical
-- toCanonical . fromCanonical ∷ Either () a → Either () a

-- The (:+:) and U1 types correspond to canonical sum and canonical unit.
-- >>> :kind! Rep Bool
-- Rep Bool ∷ Type → Type
-- = M1
--     D
--     ('MetaData "Bool" "GHC.Types" "ghc-prim" 'False)
--     (M1 C ('MetaCons "False" 'PrefixI 'False) U1
--      :+: M1 C ('MetaCons "True" 'PrefixI 'False) U1)

-- Compare this to the definition of Bool:
-- data Bool
--   = False
--   | True

-- class Generic a where
--   type Rep a ∷ Type → Type  -- the associated type `Rep a` corresponds to the canonical form of type `a`
--   from ∷ a → Rep a x        -- `from` and `to` form an isomorphism between `a` and `Rep a`
--   to   ∷ Rep a x → a

-- The extension DeriveGeneric will automatically derive an instance of Generic.

-- The associated type `Rep a` corresponds to the canonical form of the type `a`.

-- Unintuitively `to` converts to the usual `type a` form, and `from` converts from the usual form!

-- Essentially Rep Bool has this shape:
-- Rep Bool = ... (... U1 :+: ... U1)

-- The (:+:) type is the canonical analogue of the | that separates data constructors from one another.
-- Because True and False contain no information, each is isomorphic to the unit type ().
-- As a result, the canonical representation of Bool is conceptually just `Either () ()`,
-- or in its GHC.Generics form as `... (... U1 :+: ... U1)`

-------------------------------------------
-- 13.2 Deriving Structural Polymorphism --
-------------------------------------------

-- For pedagogical reasons let's write a generically Eq (GEq).

-- Cookbook recipe for deriving structural polymorphism:
-- 1. Define a typeclass to act as a carrier.
-- 2. Provide inductive instances of the class for the generic Rep constructors.
-- 3. Write a helper function to map between the Rep type and the desired type.

-----------------------------------------------
-- 1. Define a typeclass to act as a carrier --
-----------------------------------------------

-- >>> :type (==)
-- (==) ∷ Eq a ⇒ a → a → Bool

-- The type parameter `a` to GEq has kind `Type → Type`.
-- This is a quirk of GHC.Generics, and allows the same Rep machinery when dealing with higher-kinded classes.
-- When writing carrier classes for types of kind Type, we will always saturate `a` with a dummy type (`_1`).
-- whose only purpose is to make the whole thing kind check.
class GEq a where -- G stands for Generic (naming convention)
  geq ∷ a _1 → a _1 → Bool

-- >>> :kind! GEq
-- GEq ∷ (Type → Type) → Constraint
-- = GEq

----------------------------------------------------------------------------------
-- 2. Provide inductive instances of the class for the generic Rep constructors --
----------------------------------------------------------------------------------

-- U1 is used for constructors without arguments.
instance GEq U1 where
  geq ∷ U1 _1 → U1 _1 → Bool
  geq U1 U1 = True

-- V1 (Void) is used for datatypes without constructors.
instance GEq V1 where
  geq ∷ V1 _1 → V1 _1 → Bool
  geq _ _ = True

-- K1 is for concrete types, e.g. inside data constructors.
-- K1: Constants, additional parameters and recursion of kind *.
-- We fall back on an Eq (not GEq!) instance for comparison.
instance Eq a ⇒ GEq (K1 _1 a) where
  geq ∷ Eq a ⇒ K1 _1 a _2 → K1 _1 a _2 → Bool
  geq (K1 x) (K1 y) = x == y

-- But why are we using an Eq constraint rather than GEq?
-- We're using GEq to help derive Eq, which implies Eq is the actual type we care about.
-- If we were to use a GEq constraint, we'd remove the ability for anyone to write a non-generic instance of Eq!

-- Sums (:+:): encode choice between constructors.
-- (:+:) is a type operator and needs the TypeOperators extension.
-- Two sums are equal iff they are the same data constructor (left and right), and if their internal data is equal.
-- L1 and R1 are the constructors for (:+:).
instance (GEq a, GEq b) ⇒ GEq (a :+: b) where
  geq ∷ (GEq a, GEq b) ⇒ (:+:) a b x → (:+:) a b x → Bool
  geq (L1 a1) (L1 a2) = geq a1 a2
  geq (R1 b1) (R1 b2) = geq b1 b2
  geq _ _ = False

-- Products (:*:): encode multiple arguments to constructors.
instance (GEq a, GEq b) ⇒ GEq (a :*: b) where
  geq ∷ (GEq a, GEq b) ⇒ (:*:) a b _1 → (:*:) a b _1 → Bool
  geq (a1 :*: b1) (a2 :*: b2) = geq a1 a2 && geq b1 b2

-- Lift all of our GEq instances through the Rep's metadata constructors.
-- All of the types of metadata (D1, C1 and S1) are all type synonyms of M1.
-- We don't care about any metadata. We just provide an instance and ignore it.
instance GEq a ⇒ GEq (M1 _1 _2 a) where
  geq ∷ GEq a ⇒ M1 _1 _2 a _3 → M1 _1 _2 a _3 → Bool
  geq (M1 a1) (M1 a2) = geq a1 a2

---------------------------------------------------------------------------------
-- 3. Write a helper function to map between the Rep type and the desired type --
---------------------------------------------------------------------------------

genericEq ∷ (Generic a, GEq (Rep a)) ⇒ a → a → Bool
genericEq x y = geq (from x) (from y) -- from comes from typeclass Generic

-- >>> :type from
-- from ∷ Generic a ⇒ a → Rep a x

-- >>> genericEq True False
-- False

-- >>> genericEq "hello" "again"
-- False

-- >>> genericEq "hello" "hello"
-- True

-- Eq instance for Foo is now trivial.
instance (Eq a, Eq b, Eq c) ⇒ Eq (Foo a b c) where
  (==) ∷ (Eq a, Eq b, Eq c) ⇒ Foo a b c → Foo a b c → Bool
  (==) = genericEq

-- For our own typeclasses - here MyEq - we can have the compiler write that last piece of boilerplate for us.
-- data Foo a b c = F0 | F1 a | F2 b c
--   deriving (Generic, MyEq) -- just use extension DeriveAnyClass!!!

class MyEq a where
  eq ∷ a → a → Bool
  default eq ∷ (Generic a, GEq (Rep a)) ⇒ a → a → Bool
  eq = genericEq

-- >>> :type eq
-- eq ∷ MyEq a ⇒ a → a → Bool

-----------------
-- Testing Foo --
-----------------

-- >>> eq F0 F0
-- True

-- >>> eq (F1 "foo") (F1 "foo")
-- True

-- >>> eq F0 (F1 "hello")
-- False

-- >>> eq (F1 "foo") (F1 "bar")
-- False

toCanonical ∷ Maybe a → Either () a
toCanonical Nothing = Left ()
toCanonical (Just a) = Right a

fromCanonical ∷ Either () a → Maybe a
fromCanonical (Left ()) = Nothing
fromCanonical (Right a) = Just a
