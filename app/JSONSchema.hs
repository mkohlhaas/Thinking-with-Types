{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module JSONSchema where

-- JSON Schema is - in its own words - "a vocabulary that allows you to annotate and validate JSON documents."
-- It's sort of like a type system, described in JSON itself.

import Control.Monad.Writer (MonadWriter (tell), Writer, runWriter)
import Data.Aeson
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.Aeson.Key (fromText)
import Data.ByteString.Lazy.Char8 qualified as LC8
import Data.Kind (Constraint, Type)
import Data.Text
import Data.Typeable (Proxy (Proxy))
import Data.Vector (fromList)
import GHC.Generics (C, D, D1, Generic (Rep), K1, M1, Meta (MetaData, MetaSel), S, type (:*:), type (:+:))
import GHC.TypeLits (KnownSymbol, Symbol, TypeError, symbolVal)
import GHC.TypeLits qualified as Err

-- JSON schema:
-- { "title": "Person",
--   "type": "object",
--   "properties": { "name":        { "type": "string" },
--                   "age":         { "type": "integer" },
--                   "phone":       { "type": "string" },
--                   "permissions": { "type": "array", "items": { "type": "boolean" }}},
--   "required": ["name" , "age", "permissions"]
-- }

-- the corresponding Haskell datatype:
data Person = Person
  { name ∷ String,
    age ∷ Int,
    phone ∷ Maybe String,
    permissions ∷ [Bool]
  }
  deriving (Generic)

-- We want to write JSON schmema from Haskell datatype: Haskell datatype → JSON schema

-- 1. carrier typeclass
-- The [Text] will be used to track the required properties, and the Value is the schema we're building.
type GSchema ∷ (Type → Type) → Constraint
class GSchema a where
  gschema ∷ Writer [Text] Value

-- Notice that gschema doesn't reference the a type parameter anywhere.
-- While we could use a Proxy to drive the instance lookups the way we did for HasPrintf,
-- a cleaner interface is to enable AllowAmbiguousTypes and later use TypeApplications to fill in the desired variable.

-- We want to generate JSON Schema only for Haskell records.

----------------------------------------------------
-- Helper functions for manipulating JSON objects --
----------------------------------------------------

-- merge two JSON objects by taking the union of their properties
mergeObjects ∷ Value → Value → Value
mergeObjects (Object a) (Object b) = Object $ a <> b
mergeObjects _ _ = error "unsafe use of mergeObjects"

-- takes a KnownSymbol nm and tells the corresponding term-level string
emitRequired ∷ ∀ nm. KnownSymbol nm ⇒ Writer [Text] ()
emitRequired = tell . pure . pack . symbolVal $ Proxy @nm

-- >>> runWriter (emitRequired @"required property")
-- ((),["required property"])

-- symbolVal converts a SYMBOL into a String
-- >>> :type symbolVal
-- symbolVal ∷ KnownSymbol n ⇒ proxy n → String

-- >>> symbolVal (Proxy @"i am a symbol")
-- "i am a symbol"

-- The KnownSymbol stuff in symbolVal's type is simply a proof that GHC knows what SYMBOL we're talking about.
-- It will automatically generate the KnownSymbol instance for us.
-- So it's nothing we need to worry about.

-- using a closed type family to convert from Haskell type names to their JSON Schema counterparts
type ToJSONType ∷ Type → Symbol
type family ToJSONType t where
  ToJSONType Int = "integer"
  ToJSONType Integer = "integer"
  ToJSONType Float = "number"
  ToJSONType Double = "number"
  ToJSONType String = "string"
  ToJSONType Bool = "boolean"
  ToJSONType [t] = "array"
  ToJSONType t = TypeName t

-- There is no straightforward means of getting the name of a type as a symbol.
-- But we can use generic metadata to retrieve a type's name.
type TypeName t = RepName (Rep t)

type RepName ∷ (Type → Type) → Symbol
type family RepName x where
  RepName (D1 ('MetaData nm _ _ _) _) = nm

-- >>> :kind! ToJSONType Double
-- ToJSONType Double ∷ Symbol
-- = "number"

-- >>> :kind! ToJSONType String
-- ToJSONType String ∷ Symbol
-- = "string"

-- >>> :kind! ToJSONType [Int]
-- ToJSONType [Int] ∷ Symbol
-- = "array"

-- >>> :kind! ToJSONType Person
-- ToJSONType Person ∷ Symbol
-- = "Person"

-- Often objects of the form `{"type": "foo"}` are needed.
-- makeTypeObj is type-applicable, and will use the ToJSONType of the applied type.
makeTypeObj ∷ ∀ a. KnownSymbol (ToJSONType a) ⇒ Value
makeTypeObj = object ["type" .= String (pack . symbolVal $ Proxy @(ToJSONType a))]

-- >>> makeTypeObj @Int
-- Object (fromList [("type",String "integer")])

-- Wrap an object with the name of a property.
-- Used to build the "properties" property in the JSON Schema document.
makePropertyObj ∷ ∀ name. KnownSymbol name ⇒ Value → Value
makePropertyObj v = object [(fromText . pack . symbolVal $ Proxy @name) .= v]

-- >>> makePropertyObj @"age" (makeTypeObj @Int)
-- Object (fromList [("age",Object (fromList [("type",String "integer")]))])

-- # gschema Maybe
-- In order to get access to the record name, it's insufficient to simply define an instance of GSchema for K1.
-- By the time we get to K1 we've lost access to the metadata.
-- The metadata is stored in an outer wrapper.
-- Instead, we can do type-level pattern matching on `M1 S meta (K1 _ a)`.
-- The S type is used as a parameter to M1 to describe record selector metadata.
instance {-# OVERLAPPING #-} (KnownSymbol nm, KnownSymbol (ToJSONType a)) ⇒ GSchema (M1 S ('MetaSel ('Just nm) _1 _2 _3) (K1 _4 (Maybe a))) where
  gschema ∷ (KnownSymbol nm, KnownSymbol (ToJSONType a)) ⇒ Writer [Text] Value
  gschema = pure . makePropertyObj @nm $ makeTypeObj @a
  {-# INLINE gschema #-}

testPP ∷ LC8.ByteString
testPP = encodePretty $ makePropertyObj @"myproperty" (makeTypeObj @Bool)

-- >>> testPP
-- "{\n    \"myproperty\": {\n        \"type\": \"boolean\"\n    }\n}"

-- # gschema K1 generic
instance (KnownSymbol nm, KnownSymbol (ToJSONType a)) ⇒ GSchema (M1 S ('MetaSel ('Just nm) _1 _2 _3) (K1 _4 a)) where
  gschema ∷ (KnownSymbol nm, KnownSymbol (ToJSONType a)) ⇒ Writer [Text] Value
  gschema = do
    emitRequired @nm
    pure . makePropertyObj @nm $
      makeTypeObj @a
  {-# INLINE gschema #-}

-- # gschema String
instance {-# OVERLAPPING #-} KnownSymbol nm ⇒ GSchema (M1 S ('MetaSel ('Just nm) _1 _2 _3) (K1 _4 String)) where
  gschema ∷ KnownSymbol nm ⇒ Writer [Text] Value
  gschema = do
    emitRequired @nm
    pure . makePropertyObj @nm $ makeTypeObj @String
  {-# INLINE gschema #-}

-- # gschema List
instance {-# OVERLAPPING #-} (KnownSymbol nm, KnownSymbol (ToJSONType [a]), KnownSymbol (ToJSONType a)) ⇒ GSchema (M1 S ('MetaSel ('Just nm) _1 _2 _3) (K1 _4 [a])) where
  gschema ∷ (KnownSymbol nm, KnownSymbol (ToJSONType [a]), KnownSymbol (ToJSONType a)) ⇒ Writer [Text] Value
  gschema = do
    emitRequired @nm
    let innerType = object ["items" .= makeTypeObj @a]
    pure . makePropertyObj @nm . mergeObjects innerType $ makeTypeObj @[a]
  {-# INLINE gschema #-}

-- # gschema M1 C (metadata for data constructors)
instance GSchema a ⇒ GSchema (M1 C _1 a) where
  gschema ∷ GSchema a ⇒ Writer [Text] Value
  gschema = gschema @a
  {-# INLINE gschema #-}

-- # gschema M1 D (metadata for type constructors)
instance (GSchema a, KnownSymbol nm) ⇒ GSchema (M1 D ('MetaData nm _1 _2 _3) a) where
  gschema ∷ (GSchema a, KnownSymbol nm) ⇒ Writer [Text] Value
  gschema = do
    sch ← gschema @a
    pure $ object ["title" .= (String . pack . symbolVal $ Proxy @nm), "type" .= String "object", "properties" .= sch]
  {-# INLINE gschema #-}

-- # gschema Times
-- If we have a product of fields, we need to merge them together.
instance (GSchema f, GSchema g) ⇒ GSchema (f :*: g) where
  gschema = mergeObjects <$> gschema @f <*> gschema @g
  {-# INLINE gschema #-}

-- # gschema Plus
-- For coproduct types, we will simply error out as the JSON Schema documentation is conspicuously quiet about the encoding of sums.
instance (TypeError ('Err.Text "JSON Schema does not support sum types.")) ⇒ GSchema (f :+: g) where
  gschema = error "JSON Schema does not support sum types."
  {-# INLINE gschema #-}

schema ∷ ∀ a. (GSchema (Rep a), Generic a) ⇒ Value
schema =
  let (v, reqs) = runWriter $ gschema @(Rep a)
   in mergeObjects v $ object ["required" .= Array (fromList $ String <$> reqs)]
{-# INLINE schema #-}

-- >>> schema @Person
-- Object (fromList [("properties",Object (fromList [("age",Object (fromList [("type",String "integer")])),("name",Object (fromList [("type",String "string")])),("permissions",Object (fromList [("items",Object (fromList [("type",String "boolean")])),("type",String "array")])),("phone",Object (fromList [("type",String "string")]))])),("required",Array [String "name",String "age",String "permissions"]),("title",String "Person"),("type",String "object")])


-- >>> encodePretty $ schema @Person
-- "{\n    \"properties\": {\n        \"age\": {\n            \"type\": \"integer\"\n        },\n        \"name\": {\n            \"type\": \"string\"\n        },\n        \"permissions\": {\n            \"items\": {\n                \"type\": \"boolean\"\n            },\n            \"type\": \"array\"\n        },\n        \"phone\": {\n            \"type\": \"string\"\n        }\n    },\n    \"required\": [\n        \"name\",\n        \"age\",\n        \"permissions\"\n    ],\n    \"title\": \"Person\",\n    \"type\": \"object\"\n}"

-- "{
--     "properties": {
--         "age": {
--             "type": "integer"
--         },
--         "name": {
--             "type": "string"
--         },
--         "permissions": {
--             "items": {
--                 "type": "boolean"
--             },
--             "type": "array"
--         },
--         "phone": {
--             "type": "string"
--         }
--     },
--     "required": [
--         "name",
--         "age",
--         "permissions"
--     ],
--     "title": "Person",
--     "type": "object"
-- }"

-- sum types fail with a helpful error message
-- >>> schema @Bool
-- JSON Schema does not support sum types.
-- In the expression: schema @Bool
-- In an equation for `it_a4eTl': it_a4eTl = schema @Bool

