{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Kan where

import Control.Monad.Codensity
import Data.Functor.Day.Curried
import Data.Functor.Yoneda

{-

newtype Yoneda f a = Yoneda
  { runYoneda :: ∀ b. (a -> b) -> f b
  }

-- # FunctorYoneda
instance Functor (Yoneda f) where
  fmap f (Yoneda y) = Yoneda (\k -> y (k . f))

-}
