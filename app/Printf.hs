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

module Printf where

------------------------
-- AssociatedFamilies --
------------------------

-- C/C++ `printf` format strings are a sequence of interspersed types and text.
-- We can model this in Haskell by keeping a type-level list of TYPEs and SYMBOLs.
-- The TYPEs describe parameters, and the SYMBOLs are literal pieces of text to output.

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownSymbol, Nat, Symbol, symbolVal)

----------------------------------
-- Building Types from a Schema --
----------------------------------

-- We need a data structure to store the format schema of a printf call.
-- We build a binary type constructor which is polykinded in both of its parameters.
-- The goal is to build a type-safe, heterogeneously-kinded linked list.

-- type list
-- (The (:<<) symbol was chosen due to the similarly it has with C++’s `<<` output stream operator.)
-- Note: (:<<) doesn't have any data constructors. So we are unable to construct one of them at the term-level.
-- Its only purpose is to store type-level information.
type (:<<) ∷ k1 → k2 → Type
data a :<< b

infixr 5 :<<

-- k1, k2 = kinds
-- a, b   = types

-- >>> :kind (:<<)
-- (:<<) ∷ k1 → k2 → Type

-- >>> :kind! Int :<< Bool
-- Int :<< Bool ∷ Type
-- = Int :<< Bool

-- >>> :kind! Int :<< String
-- Int :<< String ∷ Type
-- = Int :<< [Char]

-- (:<<) is right associative
-- >>> :kind! Int :<< Bool :<< Int
-- Int :<< Bool :<< Int ∷ Type
-- = Int :<< (Bool :<< Int)

-- Note: "hello" is a type
-- >>> :kind! Int :<< "hello"
-- Int :<< "hello" ∷ Type
-- = Int :<< "hello"

-- (:<<) works as `cons`.
-- >>> :kind! "hello " :<< Bool :<< "!"
-- "hello " :<< Bool :<< "!" ∷ Type
-- = "hello " :<< (Bool :<< "!")

-- We need to construct the proper type signature of our formatting function.
-- E.g., from a type `Int :<< ":" :<< Bool :<< "!"`, we want to produce the type `Int → Bool → String`.
-- Literal strings will be ignored.

-- ASSOCIATED TYPE FAMILIES are types associated with a typeclass, and provide a convenient way to bundle term-level code with computed types!
-- Associated type families allow us to compute ad-hoc types!

-- associated type family
type HasPrintf ∷ k → Constraint
class HasPrintf a where -- type class with an ...
  type Printf a ∷ Type -- ... associated type; this type has to be computed by GHC; corresponds to the type of the formatting function
  -- The String parameter acts as an accumulator where we can keep track of all of the formatting done by earlier steps in the recursion.
  -- Proxy exists only to allow Haskell to find the correct instance of HasPrintf from the call-site of `format`.
  format ∷ String → Proxy a → Printf a

-- The format types will always be of the form `a :<< ... :<< "symbol"` (i.e. they always end with a SYMBOL).

-- Structural Recursion
-- Case 1: base case
instance KnownSymbol text ⇒ HasPrintf (text ∷ Symbol) where
  type Printf text = String
  -- return accumulator and append symbol as String
  format ∷ KnownSymbol text ⇒ String → Proxy text → Printf text
  format s _ = s <> symbolVal (Proxy @text)

-- Case 2: Symbol
instance (HasPrintf a, KnownSymbol text) ⇒ HasPrintf ((text ∷ Symbol) :<< a) where
  type Printf (text :<< a) = Printf a
  format s _ = format (s <> symbolVal (Proxy @text)) (Proxy @a)

-- Case 3: Type
instance (HasPrintf a, Show param) ⇒ HasPrintf ((param ∷ Type) :<< a) where
  type Printf (param :<< a) = param → Printf a
  format s _ param = format (s <> show param) (Proxy @a)

-- Case 3': Type String (to unquote Strings)
instance {-# OVERLAPPING #-} HasPrintf a ⇒ HasPrintf (String :<< a) where
  type Printf (String :<< a) = String → Printf a
  format s _ param = format (s <> param) (Proxy @a)

-- Printf(Int :<< ":" :<< Bool :<< "!")
--
-- Printf(Int :<< (":" :<< (Bool :<< "!"))) -- infixr 5
-- case 3: Int → Printf (":" :<< (Bool :<< "!"))
--
-- Printf(":" :<< (Bool :<< "!"))
-- case 2: Int → Printf (Bool :<< "!")
--
-- Printf (Bool :<< "!")
-- case 3: Int → Bool → Printf "!"
--
-- Printf "!"
-- case 1: Int → Bool → String

-- >>> :kind! Printf(Int :<< ":" :<< Bool :<< "!")
-- Printf(Int :<< ":" :<< Bool :<< "!") :: Type
-- = Int -> Bool -> [Char]

-- wrapper to hide format's accumulator
-- `Printf a` will be computed by GHC
printf ∷ HasPrintf a ⇒ Proxy a → Printf a
printf = format ""

-- >>> printf (Proxy @"test")
-- "test"

-- printf (Proxy @"test") will result in a "call" to Printf @"test"
-- GHC will compute the resulting type

-- >>> :type printf (Proxy @"test")
-- printf (Proxy @"test") :: String

-- >>> printf (Proxy @(Int :<< " + " :<< Int :<< " = 3")) 1 2
-- "1 + 2 = 3"

-- >>> :type printf (Proxy @(Int :<< " + " :<< Int :<< " = 3"))
-- printf (Proxy @(Int :<< " + " :<< Int :<< " = 3")) :: Int -> Int -> String

-- Without case 3'
-- printf (Proxy @(String :<< "world!")) "hello "
-- "\"hello \"world!"

-- >>> printf (Proxy @(String :<< "world!")) "hello "
-- "hello world!"

-- >>> :type printf (Proxy @(String :<< "world!"))
-- printf (Proxy @(String :<< "world!")) :: String -> String

wrongPrintf ∷ a → String → String
wrongPrintf _ str = show str ++ " world!"

type Pad ∷ Nat → k → Type
data Pad n a
