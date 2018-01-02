{-# OPTIONS --without-K #-}

module Data.ByteString.Primitive.Lazy where

open import Data.Word8.Primitive using (Word8)
open import Agda.Builtin.Nat using (Nat)
open import Data.Colist using (Colist)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.IO using (IO)
open import Data.Tuple.Base using (Pair)

{-# FOREIGN GHC import qualified Data.Word    #-}
{-# FOREIGN GHC import qualified Data.Text    #-}
{-# FOREIGN GHC import qualified Data.ByteString.Lazy    #-}
open import Foreign.Haskell using (Unit)

open import Data.ByteString.Primitive.Int

postulate
  ByteStringLazy : Set
  readBinaryFileLazy    : String → IO ByteStringLazy
  writeBinaryFileLazy   : String → ByteStringLazy → IO Unit
  Colist←Lazy : ByteStringLazy → Colist Word8
  Colist→Lazy : Colist Word8 → ByteStringLazy
  emptyLazy : ByteStringLazy
  nullLazy : ByteStringLazy → Bool
  lengthLazy : ByteStringLazy → Int64
  headLazy : ByteStringLazy → Word8
  tailLazy : ByteStringLazy → ByteStringLazy
  indexLazy : ByteStringLazy → Int64 → Word8
  splitAtLazy : Int64 → ByteStringLazy → Pair ByteStringLazy ByteStringLazy
  appendLazy : ByteStringLazy → ByteStringLazy → ByteStringLazy

{-# COMPILE GHC ByteStringLazy = type
    Data.ByteString.Lazy.ByteString
#-}
{-# COMPILE GHC readBinaryFileLazy = 
    ( Data.ByteString.Lazy.readFile
    . Data.Text.unpack
    )
#-}
{-# COMPILE GHC writeBinaryFileLazy =
    ( Data.ByteString.Lazy.writeFile
    . Data.Text.unpack
    )
#-}
{-# COMPILE GHC Colist←Lazy =
    ( Data.ByteString.Lazy.unpack ) #-}
{-# COMPILE GHC Colist→Lazy =
    ( Data.ByteString.Lazy.pack ) #-}
{-# COMPILE GHC emptyLazy = (Data.ByteString.Lazy.empty) #-}
{-# COMPILE GHC nullLazy = (Data.ByteString.Lazy.null) #-}
{-# COMPILE GHC lengthLazy = (Data.ByteString.Lazy.length) #-}
{-# COMPILE GHC headLazy = (Data.ByteString.Lazy.head) #-}
{-# COMPILE GHC tailLazy = (Data.ByteString.Lazy.tail) #-}
{-# COMPILE GHC indexLazy = (Data.ByteString.Lazy.index) #-}
{-# COMPILE GHC appendLazy = (Data.ByteString.Lazy.append) #-}
{-# COMPILE GHC splitAtLazy = (Data.ByteString.Lazy.splitAt) #-}

