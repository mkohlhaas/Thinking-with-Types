{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnicodeSyntax #-}

-----------------------------------
-- Chapter 4: Working with Types --
-----------------------------------

-- 4.1 Type Scoping
-- 4.2 Type Applications
-- 4.3 Ambiguous Types

module TypeApps where

import Data.Typeable

----------------------
-- 4.1 Type Scoping --
----------------------

-- Haskell uses (a generalization of) the Hindley-Milner type system and one of its features is type inference.
-- Term-level programmers don't necessarily need to annotate their functions.
-- Such an attitude is not particularly helpful for type-level programmers.

-- Hindley–Milner seems to take the view that types should be "neither seen nor heard" and an egregious
-- consequence of this is that type variables have no notion of scope.

-- There are several language extensions which can assuage this pain, the most important one being ScopedTypeVariables.

-- With ScopedTypeVariables enabled the `∀ a b` quantifier introduces a type scope and exposes the type variables `a` and `b` to the remainder of the function!
-- This allows us to reuse `b` when adding the type signature to apply, rather than introducing a new type variable.
working ∷ ∀ a b. (a → b) → a → b
working f a = apply
  where
    apply ∷ b -- same `b`
    apply = f a

-- >>> working length "hello"
-- 5

-- Behavior depends on ScopedTypeVariables!!!
broken ∷ (a → b) → a → b
broken f a = apply
  where
    -- apply ∷ b -- this is a different `b`
    apply = f a

-- >>> broken length "hello"
-- 5

-- Proxy uses phantom type `a` to transport type information.
-- data Proxy a = Proxy

-- >>> typeRep (Proxy ∷ Proxy Bool)
-- Bool

-- >>> typeRep (Proxy ∷ Proxy String)
-- [Char]

-- >>> typeRep (Proxy ∷ Proxy (Maybe [Int]))
-- Maybe [Int]

---------------------------
-- 4.2 Type Applications --
---------------------------

-- The TypeApplications extension allows us to directly apply types to expressions by prefixing a type with an `@`.

-- >>> :type fmap
-- fmap ∷ Functor f ⇒ (a → b) → f a → f b

-- set Functor f to Maybe
-- >>> :type fmap @Maybe
-- fmap @Maybe ∷ (a → b) → Maybe a → Maybe b

-- We've applied the type Maybe to the polymorphic function fmap in the same way we can apply value arguments to functions.

-- Two rules:
-- 1. Types are applied in the same order they appear in a type signature - including its context and ∀ quantifiers!
--    Type applying Int to `a → b → a`        results in `Int → b → Int`.
--    Type applying Int to `∀ b a. a → b → a` results in `a → Int → a`.
-- 2. We can avoid applying a type with an underscore: `@_`.
--    This means we can also specialize type variables which are not first in line.

-- >>> :t fmap @_ @Int @Bool
-- fmap @_ @Int @Bool ∷ Functor w ⇒ (Int → Bool) → w Int → w Bool

-- Pay attention to type order whenever you write a function that might be type applied.
-- As a guiding principle, the hardest types to infer should come first.

-------------------------
-- 4.3 Ambiguous Types --
-------------------------

-- Hindley-Milner's type inference only works to the right of the context arrow!!!
-- ⇒ the type parameter `a` in typeName can never be correctly inferred
-- Haskell refers to such a type as being AMBIGUOUS.
typeName ∷ ∀ a. Typeable a ⇒ String
typeName = show . typeRep $ Proxy @a

-- the same
-- typeName ∷ ∀ a. Typeable a ⇒ String
-- typeName = show . typeRep $ (Proxy ∷ Proxy a)

-- The AllowAmbiguousTypes extension allows to define ambiguously typed functions.

-- >>> typeName @Bool
-- "Bool"

-- >>> typeName @String
-- "[Char]"

-- >>> typeName @(Maybe [Int])
-- "Maybe [Int]"

-- ambiguous types aren’t always this obvious to spot

type family AlwaysUnit a where
  AlwaysUnit a = ()

typeSigOK1 ∷ AlwaysUnit a → a
typeSigOK1  = undefined

typeSigOK2 ∷  b → AlwaysUnit a → b
typeSigOK2 = undefined

-- if you turn AllowAmbiguousTypes off this will lead to a compiler error
-- Even though there is an `a` in the type signature, we're unable to access it.
-- `AlwaysUnit a` is equal to () for all `a`s!
typeSigNotOK ∷ Show a ⇒ AlwaysUnit a → String
typeSigNotOK = undefined

-- More specifically, the issue is that AlwaysUnit doesn't have an inverse.
-- There's no Inverse type family such that `Inverse (AlwaysUnit a)` equals `a`.
-- In mathematics, this lack of an inverse is known as NON-INJECTIVITY.

-- Because AlwaysUnit is non-injective, we're unable to learn what `a` is, given `AlwaysUnit a`.

-- Consider an analogous example from cryptography.
-- Just because you know the hash of someone's password doesn't mean you know what the password is.
-- Any good hashing function, like AlwaysUnit, is one way.
-- Just because we can go forwards doesn't mean we can also come back again.
