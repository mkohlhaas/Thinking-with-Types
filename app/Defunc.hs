{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

--------------------------------------------
-- Chapter 10: First Class Families (FCF) --
--------------------------------------------

-- 10.1 Defunctionalization
-- 10.2 Type-Level Defunctionalization
-- 10.3 Working with First Class Families
-- 10.4 Ad-Hoc Polymorphism

module Defunc where

import Prelude hiding (fst)

------------------------------
-- 10.1 Defunctionalization --
------------------------------

fst ∷ (a, b) → a
fst (a, _) = a

-- defunctionalizing `fst` by providing an EQUIVALENT LABEL
newtype Fst a b = Fst (a, b)
  deriving (Show)

-- Implementing the actual evaluation function as a typeclass.
-- The syntax `| l → t` is known as a FUNCTIONAL DEPENDENCY.
-- It states that the type `t` is fully determined by the type `l`.
-- Here, `l` is the type of our defunctionalized label Fst and `t` is the return type of the evaluation.
--     defunc label
--         | return type
--         | | functional dependency
--         | |     |
class Eval l t | l → t where
  eval ∷ l → t

instance Eval (Fst a b) a where
  eval ∷ Fst a b → a
  eval (Fst (a, _)) = a

-- >>> Fst ("hello", True)
-- Fst ("hello",True)

-- >>> eval $ Fst ("hello", True)
-- "hello"

----------------------------------------------------
-- Exercise 10.1-i: Defunctionalize `listToMaybe` --
----------------------------------------------------

listToMaybe ∷ [a] → Maybe a
listToMaybe [] = Nothing
listToMaybe (x : _) = Just x

newtype ListToMaybe a = ListToMaybe [a] deriving (Show)

instance Eval (ListToMaybe a) (Maybe a) where
  eval ∷ ListToMaybe a → Maybe a
  eval (ListToMaybe []) = Nothing
  eval (ListToMaybe (a : _)) = Just a

-- >>> eval $ ListToMaybe []
-- Nothing

-- >>> eval $ ListToMaybe [1..5]
-- Just 1

----------------------------------------------
-- Defunctionalizing Higher-Order Functions --
----------------------------------------------

-- >>> mapList fst [("hello", 1), ("world", 2)]
-- ["hello","world"]

-- >>> :type mapList fst [("hello", 1), ("world", 2)]
-- mapList fst [("hello", 1), ("world", 2)] ∷ [String]

mapList ∷ (a → b) → [a] → [b]
mapList _ [] = []
mapList f (a : as) = f a : mapList f as

data MapList a b = MapList (a → b) [a]

-- 1st attempt
-- instance Eval (MapList a b) [b] where
--   eval ∷ MapList a b → [b]
--   eval (MapList _ []) = []
--   eval (MapList f (a : as)) = f a : eval (MapList f as)

-- Fst is not evaluated
-- >>> eval (MapList Fst [("hello", 1), ("world", 2)])
-- [Fst ("hello",1),Fst ("world",2)]

-- 2nd attempt
instance (Eval b t) ⇒ Eval (MapList a b) [t] where
  eval ∷ Eval b t ⇒ MapList a b → [t]
  eval (MapList _ []) = []
  eval (MapList f (a : as)) = eval (f a) : eval (MapList f as)

-- Fst is evaluated
-- >>> eval (MapList Fst [("hello", 1), ("world", 2)])
-- ["hello","world"]
