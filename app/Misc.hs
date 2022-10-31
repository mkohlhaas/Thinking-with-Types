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

import GHC.TypeLits (ErrorMessage (ShowType, Text, (:$$:), (:<>:)), TypeError)

-- # Refl
data a :~: b where
  Refl ∷ a :~: a

---------------------------
-- Custom Error Messages --
---------------------------

-- The following four means of constructing ERRORMESSAGEs are available to us:
-- - 'Text (of kind SYMBOL → ERRORMESSAGE.) Emits the symbol verbatim. (Note that this is not Data.Text.Text.)
-- - 'ShowType (of kind K → ERRORMESSAGE.) Prints the name of the given type.
-- - '(:<>:) (of kind ERRORMESSAGE → ERRORMESSAGE → ERRORMESSAGE.) Concatenate two ERRORMESSAGEs side-by-side.
-- - '(:$$:) (of kind ERRORMESSAGE → ERRORMESSAGE → ERRORMESSAGE.) Append one ERRORMESSAGE vertically atop another.

-- custom error message
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
-- in the type 'Bool -> t_akEL[sk:1]'
-- Did you forget to specify the function you wanted?
-- When checking the inferred type
--   it_akDz :: forall {t}. (TypeError ...) => t

{-

data Maybe a
  = Just a
  | Nothing

-}
