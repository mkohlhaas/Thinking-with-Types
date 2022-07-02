{-# LANGUAGE DataKinds, UndecidableInstances, UnicodeSyntax #-}
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

{-

broken :: (a -> b) -> a -> b
broken f a = apply
  where
    apply :: b
    apply = f a

-}

working ∷ ∀ a b. (a → b) → a → b
working f a = apply
  where
    apply ∷ b
    apply = f a

{-

-- # brokenWhy
broken :: (a -> b) -> a -> b
broken f a = apply
  where
    apply :: c
    apply = f a

-}

-- # Refl
data a :~: b where
  Refl :: a :~: a

data Proxy a = Proxy

{-

data Maybe a
  = Just a
  | Nothing

-}
