module Data.ByteString.Utf8 where

open import Data.ByteString.Primitive
open import Data.String

{-# IMPORT Data.Text.Encoding #-}
postulate
  packStrict : String → ByteStringStrict
  unpackStrict : ByteStringStrict → String
{-# COMPILED packStrict (Data.Text.Encoding.encodeUtf8) #-}
{-# COMPILED unpackStrict (Data.Text.Encoding.decodeUtf8) #-}


