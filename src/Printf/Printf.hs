{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

-----------------------------------------
-- Chapter 9: Associated Type Families --
-----------------------------------------

-- 9.1 Building Types from a Schema
-- 9.2 Generating Associated Terms

module Printf where

----------------------------------------------------------------------
-- 9.1 Building Types from a Schema                                 --
-- 9.2 Generating Associated Terms (introduces the `fomat` function --
----------------------------------------------------------------------

-- C/C++ `printf` format strings are a sequence of interspersed TYPES and TEXT.
-- E.g this format string "some number: %d" corresponds Haskell to this function type `Int → String`.
-- We can model this in Haskell by keeping a type-level list of TYPEs and SYMBOLs.
-- The TYPEs describe parameters, and the SYMBOLs are literal pieces of text to output.

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownSymbol, Symbol, natVal, symbolVal)

----------------------------------
-- Building Types from a Schema --
----------------------------------

-- We need a data structure to store the format schema of a printf call.
-- We build a binary type constructor which is polykinded in both of its parameters.
-- The goal is to build a type-safe, heterogeneously-kinded linked list.

-- type-level linked list
-- The (:<<) symbol was chosen due to the similarly it has with C++’s `<<` output stream operator.
-- Note: (:<<) doesn't have any data constructors. So we are unable to construct one of them at the term-level.
-- Its only purpose is to store type-level information.
type (:<<) ∷ k1 → k2 → Type -- k1, k2, Type = kinds
data a :<< b ----------------- a,  b        = types

-- type-level operator
infixr 5 :<<

-- Notice: (:<<) doesn't have any data constructors, so we are unable to construct one of them at the term-level.
-- Its only purpose is to store type-level information.

-- >>> :kind (:<<)
-- (:<<) ∷ k1 → k2 → Type

-- >>> :kind Int :<< Bool
-- Int :<< Bool ∷ Type

-- >>> :kind Int :<< String
-- Int :<< String ∷ Type

-- (:<<) is right associative and works as `cons`.
-- >>> :kind! Int :<< Bool :<< Int
-- Int :<< Bool :<< Int ∷ Type
-- = Int :<< (Bool :<< Int)

-- >>> :kind Int :<< "hello"
-- Int :<< "hello" ∷ Type

-- We need to construct the proper type signature of our formatting function.
-- E.g., from a type `Int :<< ":" :<< Bool :<< "!"`, we want to produce the type `Int → Bool → String`.
-- Literal strings will be ignored.

-- ASSOCIATED TYPE FAMILIES are types associated with a typeclass, and provide a convenient way to bundle term-level code with computed types!
-- Associated type families allow us to compute ad-hoc types!


-- HasPrintf will create a Constraint
type HasPrintf ∷ k → Constraint
class HasPrintf a where -- type class with an ...
  type Printf a ∷ Type -- ... associated type; this type has to be computed by GHC and corresponds to the type of the formatting function
  format ∷ String → Proxy a → Printf a

-- The String parameter acts as an accumulator where we can keep track of all of the formatting done by earlier steps in the recursion.
--            |
--            |   Proxy exists only to allow Haskell to find the correct instance of HasPrintf from the call-site of `format`.
--            |         |
-- format ∷ String → Proxy a → Printf a

-- GHC's inferred (uncomment type signature in above type class) kind
-- >>> :kind HasPrintf
-- HasPrintf ∷ k → Constraint

--------------------------------------------
-- Side Note for KnownNat and KnownSymbol --
--------------------------------------------

-- class KnownNat (n ∷ Nat)
-- This class gives the integer associated with a type-level natural.
-- There are instances of the class for every concrete literal: 0, 1, 2, etc.
-- natVal ∷ ∀ n proxy. KnownNat n ⇒ proxy n → Integer

-- >>> natVal (Proxy ∷ Proxy 5)
-- 5

-- class KnownSymbol (n ∷ Symbol)
-- This class gives the string associated with a type-level symbol.
-- There are instances of the class for every concrete literal: "hello", etc.
-- symbolVal ∷ ∀ n proxy. KnownSymbol n ⇒ proxy n → String

-- >>> symbolVal (Proxy ∷ Proxy "hello")
-- "hello"

----------------------
-- End of Side Note --
----------------------

-- The format types will always be of the form `a :<< ... :<< Symbol` (i.e. they always end with a SYMBOL).

-- Structural Recursion
-- Case 1: Base case (single Symbol) (e.g. "hello")
instance KnownSymbol text ⇒ HasPrintf (text ∷ Symbol) where
  type Printf text = String
  format ∷ KnownSymbol text ⇒ String → Proxy text → Printf text -- return accumulator and append symbol as String
  format s _ = s <> symbolVal (Proxy @text)

-- Case 2: Symbol (e.g. "hello" :<< a)
instance (HasPrintf a, KnownSymbol text) ⇒ HasPrintf ((text ∷ Symbol) :<< a) where
  type Printf (text :<< a) = Printf a
  format ∷ ∀ k2 (a' ∷ k2) (text' ∷ Symbol). (HasPrintf a', KnownSymbol text') ⇒ String → Proxy (text' :<< a') → Printf (text' :<< a')
  format s _ = format (s <> symbolVal (Proxy @text)) (Proxy @a')

-- Case 3: Type (e.g. Bool :<< a, Int :<< a, etc.)
instance (HasPrintf a, Show param) ⇒ HasPrintf ((param ∷ Type) :<< a) where
  type Printf (param :<< a) = param → Printf a
  format ∷ ∀ k2 (a' ∷ k2) param'. (HasPrintf a', Show param') ⇒ String → Proxy (param' :<< a') → Printf (param' :<< a')
  format s _ param = format (s <> show param) (Proxy @a')

-- Case 3': Type String (to unquote Strings) (String :<< a)
instance {-# OVERLAPPING #-} HasPrintf a ⇒ HasPrintf (String :<< a) where
  type Printf (String :<< a) = String → Printf a
  format ∷ ∀ k2 (a' ∷ k2). HasPrintf a' ⇒ String → Proxy (String :<< a') → Printf (String :<< a')
  format s _ param = format (s <> param) (Proxy @a')

-- wrapper to hide accumulator
-- `Printf a` will be computed by GHC!!!
printf ∷ HasPrintf a ⇒ Proxy a → Printf a
printf = format ""

-- Case 1
-- >>> printf (Proxy @"test")
-- "test"

-- >>> :type printf (Proxy @"test")
-- printf (Proxy @"test") ∷ String

-- Case 2
-- >>> printf (Proxy @("hello" :<< " world"))
-- "hello world"

-- >>> :type printf (Proxy @("hello" :<< " world"))
-- printf (Proxy @("hello" :<< " world")) ∷ String

-- Case 3
-- >>> printf (Proxy @(Int :<< " world")) 42
-- "42 world"

-- >>> :type printf (Proxy @(Int :<< " world"))
-- printf (Proxy @(Int :<< " world")) ∷ Int → String

-- >>> printf (Proxy @(Int :<< " + " :<< Int :<< " = 3")) 1 2
-- "1 + 2 = 3"

-- >>> :type printf (Proxy @(Int :<< " + " :<< Int :<< " = 3"))
-- printf (Proxy @(Int :<< " + " :<< Int :<< " = 3")) ∷ Int → Int → String

-- not ending in a Symbol
-- >>> :type printf (Proxy @(Int :<< " + " :<< Int))
-- No instance for (HasPrintf Int) arising from a use of `printf'
-- In the expression: printf (Proxy @(Int :<< " + " :<< Int))

-- cheap (unpractical) workaround
-- >>> :type printf (Proxy @(Int :<< " + " :<< Int :<< ""))
-- printf (Proxy @(Int :<< " + " :<< Int :<< "")) ∷ Int → Int → String

-- without case 3'
-- printf (Proxy @(String :<< "world!")) "hello "
-- "\"hello \"world!"

-- without {-# OVERLAPPING #-} pragma in case 3'
-- >>> printf (Proxy @(String :<< "world!")) "hello "
-- Overlapping instances for HasPrintf (String :<< "world!") arising from a use of `printf' ...

-- >>> printf (Proxy @(String :<< "world!")) "hello "
-- "hello world!"

-- >>> :type printf (Proxy @(String :<< "world!"))
-- printf (Proxy @(String :<< "world!")) ∷ String → String
