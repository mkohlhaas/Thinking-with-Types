{-# LANGUAGE TemplateHaskell, TypeApplications, UnicodeSyntax #-}

module InspectionTesting where

import Data.Aeson
import JSONSchema
import Test.Inspection

mySchema ∷ Value
mySchema = schema @Person

inspect $ hasNoGenerics 'mySchema
