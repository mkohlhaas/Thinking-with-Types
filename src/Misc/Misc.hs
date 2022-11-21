{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}

------------------------------------
-- Chapter 12: Custom Type Errors --
------------------------------------

module Misc where

import GHC.TypeLits (ErrorMessage (ShowType, Text, (:$$:), (:<>:)), TypeError)

-- GHC provides the ability to construct custom type errors.
-- The module GHC.TypeLits defines the type TypeError.
-- The semantics of TypeError is that if GHC is ever asked to solve one, it emits the given type error instead, and refuse to compile.
-- Because TypeError is polykinded, we can put it anywhere we'd like at the type-level.

-- The following four means of constructing ERRORMESSAGEs are available to us:
-- - 'Text:     Emits the symbol verbatim.
-- - 'ShowType: Prints the name of the given type.
-- - '(:<>:):   Concatenate two Errormessages side-by-side. (Acts like space.)
-- - '(:$$:):   Append one Errormessage vertically atop another. (Acts like newline.)

-- >>> :kind TypeError
-- TypeError :: ErrorMessage -> b

-- >>> :kind 'Text
-- 'Text ∷ Symbol → ErrorMessage

-- >>> :kind 'ShowType
-- 'ShowType ∷ t → ErrorMessage

-- >>> :kind '(:<>:)
-- '(:<>:) ∷ ErrorMessage → ErrorMessage → ErrorMessage

-- >>> :kind '(:$$:)
-- '(:$$:) ∷ ErrorMessage → ErrorMessage → ErrorMessage

-- TypeError is usually used as a constraint in an instance context, or as the result of a type family.

-- Custom Error Message
-- TypeError as a constraint in an instance
instance
  ( TypeError
      ( 'Text "Attempting to interpret a number as a function"
          ':$$: 'Text "in the type '"
            ':<>: 'ShowType (a → b)
            ':<>: 'Text "'"
          ':$$: 'Text "Did you forget to specify the function you wanted?"
      )
  ) ⇒
  Num (a → b)

-- >>> 1 True
-- Attempting to interpret a number as a function
-- in the type 'Bool → t_akEL[sk:1]'
-- Did you forget to specify the function you wanted?
-- When checking the inferred type
--   it_akDz ∷ ∀ {t}. (TypeError ...) ⇒ t

{-

data Maybe a
  = Just a
  | Nothing

-}
