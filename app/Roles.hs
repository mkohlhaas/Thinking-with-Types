{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnicodeSyntax #-}

module Roles where

import Data.Coerce (coerce)
import Data.Monoid (Sum (..))

{-

newtype ZipList a = ZipList
  { getZipList ∷ [a]
  }

newtype Sum a = Sum
  { getSum ∷ a
  }

coerce ∷ Coercible a b ⇒ a → b

insert ∷ Ord k ⇒ k → v → Map k v → Map k v

-}

slowSum ∷ [Int] → Int
slowSum = getSum . mconcat . fmap Sum

fastSum ∷ [Int] → Int
fastSum = getSum . mconcat . coerce

newtype Reverse a = Reverse {getReverse ∷ a}
  deriving (Eq, Show)

-- # OrdReverse
instance Ord a ⇒ Ord (Reverse a) where
  compare (Reverse a) (Reverse b) = compare b a

type family IntToBool a where
  IntToBool Int = Bool
  IntToBool a = a

data BST v = Empty | Branch (BST v) v (BST v)

-- # role
type role BST nominal
