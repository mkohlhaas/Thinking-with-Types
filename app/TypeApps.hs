{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UnicodeSyntax #-}

module TypeApps where

import Data.Typeable

typeName ∷ ∀ a. Typeable a ⇒ String -- ! 1
typeName = show . typeRep $ Proxy @a -- ! 2
