{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UnicodeSyntax #-}

module TypeApps where

import Data.Typeable

-- Because Hindley-Milner's type inference only works to the right of the context arrow,
-- it means the type parameter a in typeName can never be correctly inferred.
-- Haskell refers to such a type as being ambiguous.
typeName ∷ ∀ a. Typeable a ⇒ String
typeName = show . typeRep $ Proxy @a

-- AllowAmbiguousTypes allows us to define ambiguously typed functions, and
-- TypeApplications enables us to call them.

-- >>> typeName @Bool
-- "Bool"

-- >>> typeName @String
-- "[Char]"

-- >>> typeName @(Maybe [Int])
-- "Maybe [Int]"

-- >>> typeName @ThereIsNoFoo
-- Not in scope: type constructor or class `ThereIsNoFoo'

