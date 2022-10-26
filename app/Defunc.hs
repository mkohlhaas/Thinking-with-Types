{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module Defunc where

import Prelude hiding (fst)

fst ∷ (a, b) → a
fst (a, _) = a

-- defunctionalizing `fst` by providing an equivalent label
newtype Fst a b = Fst (a, b)

-- implementing the actual evaluation function as a typeclass
-- The syntax `| l → t` is known as a FUNCTIONAL DEPENDENCY.
-- It states that the type `t` is fully determined by the type `l`.
-- Here, l is the type of our defunctionalized label - Fst - and `t` is the return type of the evaluation.
class Eval l t | l → t where
  eval ∷ l → t

instance Eval (Fst a b) a where
  eval ∷ Fst a b → a
  eval (Fst (a, _)) = a

-- >>> eval (Fst ("hello" , True))
-- "hello"

-- Exercise 10.1-i: Defunctionalize `listToMaybe ∷ [a] → Maybe a`
listToMaybe ∷ [a] → Maybe a
listToMaybe [] = Nothing
listToMaybe (x : _) = Just x

newtype ListToMaybe a = ListToMaybe [a]

instance Eval (ListToMaybe a) (Maybe a) where
  eval ∷ ListToMaybe a → Maybe a
  eval (ListToMaybe []) = Nothing
  eval (ListToMaybe (a : _)) = Just a

-- defunctionalizing higher-order functions
mapList ∷ (a → b) → [a] → [b]
mapList _ [] = []
mapList f (a : as) = f a : mapList f as

-- >>> mapList fst [("hello", 1), ("world", 2)]

data MapList a b = MapList (a → b) [a]

-- instance Eval (MapList a b) [b] where
--   eval ∷ MapList a b → [b]
--   eval (MapList _ []) = []
--   eval (MapList f (a : as)) = f a : eval (MapList f as)

-- >>> eval (MapList Fst [("hello", 1), ("world", 2)])
-- No instance for (Show (Fst String Integer))
--   arising from a use of `evalPrint'
-- In a stmt of an interactive GHCi command: evalPrint it_a7D5

-- apart from the missing Show instance we should actually also eval Fst
instance (Eval b t) ⇒ Eval (MapList a b) [t] where
  eval ∷ Eval b t ⇒ MapList a b → [t]
  eval (MapList _ []) = []
  eval (MapList f (a : as)) = eval (f a) : eval (MapList f as)

-- >>> eval (MapList Fst [("hello", 1), ("world", 2)])
-- ["hello","world"]
