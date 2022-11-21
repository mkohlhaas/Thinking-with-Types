{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
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
{-# LANGUAGE NoStarIsType #-}

--------------------------
-- Chapter 13: Generics --
--------------------------

-- 13.1 Generic Representations
-- 13.2 Deriving Structural Polymorphism
-- 13.3 Using Generic Metadata
-- 13.4 Performance
-- 13.5 Kan Extensions

module JSONSchema where

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

---------------------------------
-- 13.3 Using Generic Metadata --
---------------------------------

-- JSON Schema is - in its own words - "a vocabulary that allows you to annotate and validate JSON documents".
-- It's sort of like a type system, described in JSON itself.

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
  { name ∷ !String,
    age ∷ !Int,
    phone ∷ !(Maybe String),
    permissions ∷ ![Bool]
  }
  -- deriving (Generic) ---------------- before
  deriving (Generic, ToJSONSchema) -- after

-- We want to write JSON schema from Haskell datatype (Haskell datatype → JSON schema).

--------------------------
-- 1. Carrier Typeclass --
--------------------------

-- [Text] will be used to track the required properties, and the Value is the schema we're building.
type GSchema ∷ (Type → Type) → Constraint
class GSchema a where
  gschema ∷ Writer [Text] Value

-- Notice that gschema doesn't reference the `a` type parameter anywhere.
-- While we could use a Proxy to drive the instance lookups the way we did for HasPrintf,
-- a cleaner interface is to enable AllowAmbiguousTypes and later (in function schema) use TypeApplications to fill in the desired variable.

----------------------------------------------------
-- Helper functions for manipulating JSON objects --
----------------------------------------------------

-- >>> :type object
-- object ∷ [Pair] → Value

-- >>> :type object ["name" .= "hello"]
-- object ["name" .= "hello"] ∷ Value

-- >>> object ["name" .= "hello"]
-- Object (fromList [("name",String "hello")])

-- >>> let object1 = object ["fst_name" .= "Michael"]
-- >>> let object2 = object ["snd_name" .= "Kohlhaas"]
-- >>> mergeObjects object1 object2
-- Object (fromList [("fst_name",String "Michael"),("snd_name",String "Kohlhaas")])

-- >>> let object1 = object ["name" .= "Michael"]
-- >>> let object2 = object ["name" .= "Kohlhaas"]
-- >>> mergeObjects object1 object2
-- Object (fromList [("name",String "Michael")])

-- merge two JSON objects by taking the union of their properties
mergeObjects ∷ Value → Value → Value
mergeObjects (Object a) (Object b) = Object $ a <> b
mergeObjects _ _ = error "unsafe use of mergeObjects"

-- takes a `KnownSymbol ks` and tells the corresponding term-level string
emitRequired ∷ ∀ symbol. KnownSymbol symbol ⇒ Writer [Text] ()
emitRequired = tell . pure . pack . symbolVal $ Proxy @symbol

-- >>> runWriter $ emitRequired @"required property"
-- ((),["required property"])

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

-- There is no straightforward means of getting the name of a type as a Symbol.
-- But we can use generic metadata to retrieve a type's name.
type TypeName t = RepName (Rep t)

-- >>> :kind! Rep Person
-- Rep Person ∷ Type → Type
-- = M1
--     D
--     ('MetaData "Person" "JSONSchema" "main" 'False)
--     (M1
--        C
--        ('MetaCons "Person" 'PrefixI 'True)
--        ((M1
--            S
--            ('MetaSel
--               ('Just "name")
--               'NoSourceUnpackedness
--               'NoSourceStrictness
--               'DecidedLazy)
--            (K1 R [Char])
--          :*: M1
--                S
--                ('MetaSel
--                   ('Just "age")
--                   'NoSourceUnpackedness
--                   'NoSourceStrictness
--                   'DecidedLazy)
--                (K1 R Int))
--         :*: (M1
--                S
--                ('MetaSel
--                   ('Just "phone")
--                   'NoSourceUnpackedness
--                   'NoSourceStrictness
--                   'DecidedLazy)
--                (K1 R (Maybe [Char]))
--              :*: M1
--                    S
--                    ('MetaSel
--                       ('Just "permissions")
--                       'NoSourceUnpackedness
--                       'NoSourceStrictness
--                       'DecidedLazy)
--                    (K1 R [Bool]))))

-- D1 is a type alias for `M1 D`
type RepName ∷ (Type → Type) → Symbol
type family RepName _1 where
  RepName (D1 ('MetaData ks _ _ _) _) = ks

-- >>> :kind! ToJSONType Double
-- ToJSONType Double ∷ Symbol
-- = "number"

-- >>> :kind! ToJSONType String
-- ToJSONType String ∷ Symbol
-- = "string"

-- >>> :kind! ToJSONType Bool
-- ToJSONType Bool ∷ Symbol
-- = "boolean"

-- >>> :kind! ToJSONType [Bool]
-- ToJSONType [Bool] ∷ Symbol
-- = "array"

-- >>> :kind! ToJSONType [Int]
-- ToJSONType [Int] ∷ Symbol
-- = "array"

-- >>> :kind! ToJSONType Person
-- ToJSONType Person ∷ Symbol
-- = "Person"

---------------------------------------------------------------
-- Helper Functions for Creating Objects and Pretty Printing --
---------------------------------------------------------------

-- Often objects of the form `{"type": "foo"}` are needed.
-- makeTypeObj is type-applicable, and will use the ToJSONType of the applied type.
makeTypeObj ∷ ∀ a. KnownSymbol (ToJSONType a) ⇒ Value
makeTypeObj = object ["type" .= String (pack . symbolVal $ Proxy @(ToJSONType a))]

-- >>> makeTypeObj @Int
-- Object (fromList [("type",String "integer")])

-- >>> makeTypeObj @String
-- Object (fromList [("type",String "string")])

-- >>> makeTypeObj @Bool
-- Object (fromList [("type",String "boolean")])

-- Wrap an object with the name of a property.
-- Used to build the "properties" property in the JSON Schema document.
makePropertyObj ∷ ∀ name. KnownSymbol name ⇒ Value → Value
makePropertyObj v = object [(fromText . pack . symbolVal $ Proxy @name) .= v]

-- >>> makePropertyObj @"age" (makeTypeObj @Int)
-- Object (fromList [("age",Object (fromList [("type",String "integer")]))])

testPP ∷ LC8.ByteString
testPP = encodePretty $ makePropertyObj @"myproperty" (makeTypeObj @Bool)

-- >>> testPP
-- "{\n    \"myproperty\": {\n        \"type\": \"boolean\"\n    }\n}"

-- We want to generate JSON Schema only for Haskell records.
-- In order to get access to the record name we pattern match on `M1 S meta (K1 _ a)`.
-- The S type is used as a parameter to M1 to describe record selector metadata.

----------------------------------------------------------------------------------
-- 2. Provide inductive instances of the class for the generic Rep constructors --
----------------------------------------------------------------------------------

-- GSchema K1 generic
instance (KnownSymbol ks, KnownSymbol (ToJSONType a)) ⇒ GSchema (M1 S ('MetaSel ('Just ks) _1 _2 _3) (K1 _4 a)) where
  gschema ∷ (KnownSymbol ks, KnownSymbol (ToJSONType a)) ⇒ Writer [Text] Value
  gschema = do
    emitRequired @ks
    pure . makePropertyObj @ks $ makeTypeObj @a
  {-# INLINE gschema #-}

-- GSchema K1 Maybe
instance {-# OVERLAPPING #-} (KnownSymbol ks, KnownSymbol (ToJSONType a)) ⇒ GSchema (M1 S ('MetaSel ('Just ks) _1 _2 _3) (K1 _4 (Maybe a))) where
  gschema ∷ (KnownSymbol ks, KnownSymbol (ToJSONType a)) ⇒ Writer [Text] Value
  gschema = pure . makePropertyObj @ks $ makeTypeObj @a
  {-# INLINE gschema #-}

-- GSchema K1 String
instance {-# OVERLAPPING #-} KnownSymbol ks ⇒ GSchema (M1 S ('MetaSel ('Just ks) _1 _2 _3) (K1 _4 String)) where
  gschema ∷ KnownSymbol ks ⇒ Writer [Text] Value
  gschema = do
    emitRequired @ks
    pure . makePropertyObj @ks $ makeTypeObj @String
  {-# INLINE gschema #-}

-- GSchema K1 List
instance {-# OVERLAPPING #-} (KnownSymbol ks, KnownSymbol (ToJSONType [a]), KnownSymbol (ToJSONType a)) ⇒ GSchema (M1 S ('MetaSel ('Just ks) _1 _2 _3) (K1 _4 [a])) where
  gschema ∷ (KnownSymbol ks, KnownSymbol (ToJSONType [a]), KnownSymbol (ToJSONType a)) ⇒ Writer [Text] Value
  gschema = do
    emitRequired @ks
    let innerType = object ["items" .= makeTypeObj @a]
    pure . makePropertyObj @ks . mergeObjects innerType $ makeTypeObj @[a]
  {-# INLINE gschema #-}

-- GSchema M1 C (metadata for data constructors)
instance GSchema a ⇒ GSchema (M1 C _1 a) where
  gschema ∷ GSchema a ⇒ Writer [Text] Value
  gschema = gschema @a
  {-# INLINE gschema #-}

-- GSchema M1 D (metadata for type constructors)
instance (GSchema a, KnownSymbol ks) ⇒ GSchema (M1 D ('MetaData ks _1 _2 _3) a) where
  gschema ∷ (GSchema a, KnownSymbol ks) ⇒ Writer [Text] Value
  gschema = do
    sch ← gschema @a
    pure $
      object
        [ "title" .= (String . pack . symbolVal $ Proxy @ks),
          "type" .= String "object",
          "properties" .= sch
        ]
  {-# INLINE gschema #-}

-- GSchema Product Type
-- If we have a product of fields, we need to merge them together.
instance (GSchema f, GSchema g) ⇒ GSchema (f :*: g) where
  gschema = mergeObjects <$> gschema @f <*> gschema @g
  {-# INLINE gschema #-}

-- GSchema Sum Type
-- For coproduct types, we will simply error out as the JSON Schema documentation is conspicuously quiet about the encoding of sums.
instance (TypeError ('Err.Text "JSON Schema does not support sum types.")) ⇒ GSchema (f :+: g) where
  gschema = error "JSON Schema does not support sum types."
  {-# INLINE gschema #-}

---------------------------------------------------------------------------------
-- 3. Write a helper function to map between the Rep type and the desired type --
---------------------------------------------------------------------------------

genericSchema ∷ ∀ a. (GSchema (Rep a), Generic a) ⇒ Value
genericSchema =
  let (v, reqs) = runWriter $ gschema @(Rep a)
   in mergeObjects v $ object ["required" .= Array (fromList $ String <$> reqs)]
{-# INLINE genericSchema #-}

-- >>> genericSchema @Person
-- Object (fromList [("properties",Object (fromList [("age",Object (fromList [("type",String "integer")])),("name",Object (fromList [("type",String "string")])),("permissions",Object (fromList [("items",Object (fromList [("type",String "boolean")])),("type",String "array")])),("phone",Object (fromList [("type",String "string")]))])),("required",Array [String "name",String "age",String "permissions"]),("title",String "Person"),("type",String "object")])

-- >>> encodePretty $ genericSchema @Person
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
-- In an equation for `it_a4jJB': it_a4jJB = schema @Bool

-- automatic derivation with extension DeriveAnyClass
class ToJSONSchema a where
  schema ∷ Value
  default schema ∷ (GSchema (Rep a), Generic a) ⇒ Value
  schema = genericSchema @a

-- >>> schema @Person
-- Object (fromList [("properties",Object (fromList [("age",Object (fromList [("type",String "integer")])),("name",Object (fromList [("type",String "string")])),("permissions",Object (fromList [("items",Object (fromList [("type",String "boolean")])),("type",String "array")])),("phone",Object (fromList [("type",String "string")]))])),("required",Array [String "name",String "age",String "permissions"]),("title",String "Person"),("type",String "object")])

-- >>> encodePretty $ schema @Person
-- "{\n    \"properties\": {\n        \"age\": {\n            \"type\": \"integer\"\n        },\n        \"name\": {\n            \"type\": \"string\"\n        },\n        \"permissions\": {\n            \"items\": {\n                \"type\": \"boolean\"\n            },\n            \"type\": \"array\"\n        },\n        \"phone\": {\n            \"type\": \"string\"\n        }\n    },\n    \"required\": [\n        \"name\",\n        \"age\",\n        \"permissions\"\n    ],\n    \"title\": \"Person\",\n    \"type\": \"object\"\n}"

data User = User
  { login ∷ !String,
    password ∷ !String,
    isAdmin ∷ !Bool
  }
  deriving (Generic, ToJSONSchema)

-- >>> schema @User
-- Object (fromList [("properties",Object (fromList [("isAdmin",Object (fromList [("type",String "boolean")])),("login",Object (fromList [("type",String "string")])),("password",Object (fromList [("type",String "string")]))])),("required",Array [String "login",String "password",String "isAdmin"]),("title",String "User"),("type",String "object")])

-- >>> encodePretty $ schema @User
-- "{\n    \"properties\": {\n        \"isAdmin\": {\n            \"type\": \"boolean\"\n        },\n        \"login\": {\n            \"type\": \"string\"\n        },\n        \"password\": {\n            \"type\": \"string\"\n        }\n    },\n    \"required\": [\n        \"login\",\n        \"password\",\n        \"isAdmin\"\n    ],\n    \"title\": \"User\",\n    \"type\": \"object\"\n}"

-- "{
--     "properties": {
--         "isAdmin": {
--             "type": "boolean"
--         },
--         "login": {
--             "type": "string"
--         },
--         "password": {
--             "type": "string"
--         }
--     },
--     "required": [
--         "login",
--         "password",
--         "isAdmin"
--     ],
--     "title": "User",
--     "type": "object"
-- }"
