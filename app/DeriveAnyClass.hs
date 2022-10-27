{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module DeriveAnyClass where

import GHC.Generics

-- Foo
data Foo a b c = F0 | F1 a | F2 b c
  deriving (Generic, MyEq)

-- Eq Foo
-- Writing this instance is just mechanic.
-- We can do this using Generics.
-- instance (Eq a, Eq b, Eq c) ⇒ Eq (Foo a b c) where
--   (==) ∷ (Eq a, Eq b, Eq c) ⇒ Foo a b c → Foo a b c → Bool
--   F0 == F0 = True
--   F1 a1 == F1 a2 = a1 == a2
--   F2 b1 c1 == F2 b2 c2 = b1 == b2 && c1 == c2
--   _ == _ = False

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

-- >>> :type  toCanonical . fromCanonical
-- toCanonical . fromCanonical ∷ Either () a → Either () a

-- All types have a canonical representation as a sum-of-products.
-- They can all be built from Eithers of pairs.

-- The interesting parts of this are the (:+:) and U1 types.
-- These correspond to the canonical sum and canonical unit.
-- >>> :kind! Rep Bool
-- Rep Bool ∷ * → *
-- = M1
--     D
--     ('MetaData "Bool" "GHC.Types" "ghc-prim" 'False)
--     (M1 C ('MetaCons "False" 'PrefixI 'False) U1
--      :+: M1 C ('MetaCons "True" 'PrefixI 'False) U1)

-- Essentially it has this shape:
-- Rep Bool
-- = ...
--   (   ... U1
--   :+: ... U1
--   )

-- The (:+:) type is the canonical analogue of the | that separates data constructors from one another.
-- Because True and False contain no information, each is isomorphic to the unit type ().
-- As a result, the canonical representation of Bool is conceptually just `Either () ()`,
-- or in its GHC.Generics form as `... (... U1 :+: ... U1)`

-- Cookbook recipe for deriving structural polymorphism:
-- 1. Define a typeclass to act as a carrier.
-- 2. Provide inductive instances of the class for the generic Rep constructors.
-- 3. Write a helper function to map between the Rep and the desired type.

-- 1. Define a typeclass to act as a carrier.
-- The type parameter `a` to GEq has kind `TYPE → TYPE`.
-- This is a quirk of GHC.Generics, and allows the same Rep machinery when dealing with higher-kinded classes.
-- When writing carrier classes for types of kind TYPE, we will always saturate `a` with a dummy type `x`
-- whose only purpose is to make the whole thing kind check.
class GEq a where
  geq :: a x -> a x -> Bool

-- 2. Provide inductive instances of the class for the generic Rep constructors.
-- U1 is used for constructors without arguments.
instance GEq U1 where
  geq :: U1 x -> U1 x -> Bool
  geq U1 U1 = True

-- V1 (Void) is used for datatypes without constructors.
instance GEq V1 where
  geq :: V1 x -> V1 x -> Bool
  geq _ _ = True

-- K1 is for concrete types, e.g. inside data constructors.
-- K1: Constants, additional parameters and recursion of kind.
-- We fall back on an Eq (not GEq!) instance for comparison.
instance Eq a => GEq (K1 _1 a) where
  geq :: Eq a => K1 _1 a x -> K1 _1 a x -> Bool
  geq (K1 a) (K1 b) = a == b

-- Sums (:+:): encode choice between constructors.
-- (:+:) is a type operator and needs the TypeOperators extension.
-- Two sums are equal iff they are the same data constructor (left and right), and if their internal data is equal.
-- L1 and R1 are the constructors for (:+:).
instance (GEq a, GEq b) => GEq (a :+: b) where
  geq :: (GEq a, GEq b) => (:+:) a b x -> (:+:) a b x -> Bool
  geq (L1 a1) (L1 a2) = geq a1 a2
  geq (R1 b1) (R1 b2) = geq b1 b2
  geq _ _ = False

-- Products (:*:): encode multiple arguments to constructors
instance (GEq a, GEq b) => GEq (a :*: b) where
  geq :: (GEq a, GEq b) => (:*:) a b x -> (:*:) a b x -> Bool
  geq (a1 :*: b1) (a2 :*: b2) = geq a1 a2 && geq b1 b2

-- Lift all of our GEq instances through the Rep's metadata constructors
-- All of the types of metadata (D1, C1 and S1) are all type synonyms of M1.
-- We don't care about any metadata.
instance GEq a => GEq (M1 _x _y a) where
  geq :: GEq a => M1 _x _y a x -> M1 _x _y a x -> Bool
  geq (M1 a1) (M1 a2) = geq a1 a2

-- 3. Write a helper function to map between the Rep and the desired type.
genericEq :: (Generic a, GEq (Rep a)) => a -> a -> Bool
genericEq a b = geq (from a) (from b) -- `from` is a dummy type

-- >>> genericEq True False
-- False

-- >>> genericEq "hello" "again"
-- False

-- >>> genericEq "hello" "hello"
-- True

class MyEq a where
  eq :: a -> a -> Bool
  default eq :: (Generic a, GEq (Rep a)) => a -> a -> Bool
  eq a b = geq (from a) (from b)

-- >>> :type eq
-- eq :: MyEq a => a -> a -> Bool

-- >>> eq F0 F0
-- True

-- >>> eq (F1 "foo") (F1 "foo")
-- True

-- >>> eq F0 (F1 "hello")
-- False

-- >>> eq (F1 "foo") (F1 "bar")
-- False

-- For our own typeclasses we can go further and have the compiler actually write that last piece of boilerplate for us too.
-- data Foo a b c = F0 | F1 a | F2 b c
--   deriving (Generic, MyEq) -- just use extension DeriveAnyClass!!!

instance (Eq a, Eq b, Eq c) => Eq (Foo a b c) where
  (==) = genericEq

toCanonical :: Maybe a -> Either () a
toCanonical Nothing = Left ()
toCanonical (Just a) = Right a

fromCanonical :: Either () a -> Maybe a
fromCanonical (Left ()) = Nothing
fromCanonical (Right a) = Just a

{-

-- The extension DeriveGeneric will automatically derive an instance of Generic.

class Generic a where
  type Rep a ∷ Type → Type  -- the associated type `Rep a` corresponds to the canonical form of type `a`
  from ∷ a → Rep a x        -- `from` and `to` form an isomorphism between `a` and `Rep a`
  to   ∷ Rep a x → a

Unintuitively `to` converts to the usual `type a` form, and `from` converts from the usual form!

-}
