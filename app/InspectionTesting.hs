{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UnicodeSyntax #-}

--------------------------
-- Chapter 13: Generics --
--------------------------

-- 13.1 Generic Representations
-- 13.2 Deriving Structural Polymorphism
-- 13.3 Using Generic Metadata
-- 13.4 Performance
-- 13.5 Kan Extensions

module InspectionTesting where

import Data.Aeson
import JSONSchema
import Test.Inspection

----------------------
-- 13.4 Performance --
----------------------

mySchema :: Value
mySchema = schema @Person

inspect $ hasNoGenerics 'mySchema
