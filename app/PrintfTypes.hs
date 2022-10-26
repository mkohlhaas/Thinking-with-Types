{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE InstanceSigs #-}

module PrintfTypes where

------------------------
-- AssociatedFamilies --
------------------------

-- `printf` format strings are a sequence of types and text to intersperse between them.
-- We can model this in Haskell by keeping a type-level list of TYPEs and SYMBOLs.
-- The TYPEs describe parameters, and the SYMBOLs are literal pieces of text to output.

import Data.Kind (Constraint, Type)
import GHC.TypeLits (Symbol)

----------------------------------
-- Building Types from a Schema --
----------------------------------

-- We need a data structure to store the format schema of a printf call.
-- We build a binary type constructor which is polykinded in both of its parameters.
-- The goal is to build a type-safe, heterogeneously-kinded linked list.

-- # Type List
-- The (:<<) symbol was chosen due to the similarly it has with C++’s `<<` output stream operator.
-- Notice here that (:<<) doesn't have any data constructors, so we are unable to construct one of them at the term-level.
-- Its only purpose is to store type-level information.
data (a ∷ k1) :<< (b ∷ k2)

infixr 5 :<<

-- >>> :kind (:<<)
-- (:<<) ∷ k1 → k2 → Type

-- (:<<) works as a cons cell for our linked list.
-- We can chain them together indefinitely and store everything we want at the type-level.
-- >>> :kind! "hello " :<< String :<< "!"
-- "hello " :<< String :<< "!" ∷ Type
-- = "hello " :<< ([Char] :<< "!")

-- We need to construct the proper type signature of our formatting function.
-- E.g., from a type `Int :<< ":" :<< Bool :<< "!"`, we want to produce the type `Int → Bool → String`.

-- ASSOCIATED TYPE FAMILIES are associated with a typeclass, and provide a convenient way to bundle term-level code with computed types.
-- Associated type families allow us to compute ad-hoc types.

-- associated type family
type HasPrintf ∷ k → Constraint
class HasPrintf a where -- type class with an ...
  type Printf a ∷ Type -- ... associated type; corresponds to the desired type of the formatting function

-- Our format types will always be of the form `a :<< ... :<< "symbol"` (they always end with a SYMBOL).

-- Structural Recursion
-- base case (case 1)
instance HasPrintf (text ∷ Symbol) where
  type Printf text = String

-- Symbol (case 2)
instance HasPrintf a ⇒ HasPrintf ((text ∷ Symbol) :<< a) where
  type Printf (text :<< a) = Printf a

-- Type (case 3)
instance HasPrintf a ⇒ HasPrintf ((param ∷ Type) :<< a) where
  type Printf (param :<< a) = param → Printf a

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

-- Printf "!"
-- case 1: Int → Bool → String

-- >>> :kind! Printf(Int :<< ":" :<< Bool :<< "!")
-- Printf(Int :<< ":" :<< Bool :<< "!") ∷ *
-- = Int → Bool → [Char]

type family AlwaysUnit a where
  AlwaysUnit a = ()

class TypeName a where
  typeName ∷ AlwaysUnit a → String

-- # TypeNameString
instance TypeName String where
  typeName ∷ AlwaysUnit String → String
  typeName _ = "String"

-- # TypeNameBool
instance TypeName Bool where
  typeName ∷ AlwaysUnit Bool → String
  typeName _ = "Bool"

{-

name ∷ String
name = typeName ()

-}
