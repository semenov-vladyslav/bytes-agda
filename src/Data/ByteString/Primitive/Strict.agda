{-# OPTIONS --without-K #-}

module Data.ByteString.Primitive.Strict where

open import Data.Word8.Primitive using (Word8)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.IO using (IO)
open import Data.Tuple.Base using (Pair)

{-# FOREIGN GHC import qualified Data.Word    #-}
{-# FOREIGN GHC import qualified Data.Text    #-}
{-# FOREIGN GHC import qualified Data.ByteString    #-}
open import Foreign.Haskell using (Unit)

open import Data.ByteString.Primitive.Int

postulate
  ByteStringStrict : Set
  readBinaryFileStrict    : String → IO ByteStringStrict
  writeBinaryFileStrict   : String → ByteStringStrict → IO Unit
  List←Strict : ByteStringStrict → List Word8
  List→Strict : List Word8 → ByteStringStrict
  emptyStrict : ByteStringStrict
  nullStrict : ByteStringStrict → Bool
  lengthStrict : ByteStringStrict → Int
  headStrict : ByteStringStrict → Word8
  tailStrict : ByteStringStrict → ByteStringStrict
  indexStrict : ByteStringStrict → Int → Word8
  splitAtStrict : Int → ByteStringStrict → Pair ByteStringStrict ByteStringStrict

{-# COMPILE GHC ByteStringStrict = type
    Data.ByteString.ByteString
#-}
{-# COMPILE GHC readBinaryFileStrict =
    ( Data.ByteString.readFile
    . Data.Text.unpack
    )
#-}
{-# COMPILE GHC writeBinaryFileStrict =
    ( Data.ByteString.writeFile
    . Data.Text.unpack
    )
#-}
{-# COMPILE GHC List←Strict =
    ( Data.ByteString.unpack ) #-}
{-# COMPILE GHC List→Strict =
    ( Data.ByteString.pack ) #-}
{-# COMPILE GHC emptyStrict = (Data.ByteString.empty) #-}
{-# COMPILE GHC nullStrict = (Data.ByteString.null) #-}
{-# COMPILE GHC lengthStrict = (Data.ByteString.length) #-}
{-# COMPILE GHC headStrict = (Data.ByteString.head) #-}
{-# COMPILE GHC tailStrict = (Data.ByteString.tail) #-}
{-# COMPILE GHC indexStrict = (Data.ByteString.index) #-}
{-# COMPILE GHC splitAtStrict = (Data.ByteString.splitAt) #-}

