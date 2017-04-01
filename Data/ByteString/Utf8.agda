module Data.ByteString.Utf8 where

open import Data.ByteString.Primitive
open import Data.String

{-# FOREIGN GHC import qualified Data.ByteString #-}
{-# FOREIGN GHC import qualified Data.Text.Encoding #-}
postulate
  packStrict : String → ByteStringStrict
  unpackStrict : ByteStringStrict → String
{-# COMPILE GHC packStrict = (Data.Text.Encoding.encodeUtf8) #-}
{-# COMPILE GHC unpackStrict = (Data.Text.Encoding.decodeUtf8) #-}


