module Data.ByteString.Primitive where

open import Data.Word using (Word8)
open import Data.Nat using (ℕ)
open import Data.Colist using (Colist)
open import Data.List using (List)
open import Data.String using (String)

{-# IMPORT Data.Text    #-}
{-# IMPORT Data.ByteString.Lazy    #-}
{-# IMPORT Data.ByteString    #-}
open import IO.Primitive using (IO)
open import Foreign.Haskell using (Unit)

{-# IMPORT Data.Int #-}
postulate
  Int : Set
  Int64 : Set
  intToℕ : Int → ℕ
  int64Toℕ : Int64 → ℕ
{-# COMPILED_TYPE Int (Prelude.Int) #-}
{-# COMPILED_TYPE Int64 (Data.Int.Int64) #-}
{-# COMPILED intToℕ (Prelude.fromIntegral) #-}
{-# COMPILED int64Toℕ (Prelude.fromIntegral) #-}

postulate
  ByteStringLazy : Set
  readBinaryFileLazy    : String → IO ByteStringLazy
  writeBinaryFileLazy   : String → ByteStringLazy → IO Unit
  Colist←Lazy : ByteStringLazy → Colist Word8
  Colist→Lazy : Colist Word8 → ByteStringLazy
  emptyLazy : ByteStringLazy
  lengthLazy : ByteStringLazy → Int64

{-# COMPILED_TYPE ByteStringLazy 
    Data.ByteString.Lazy.ByteString
#-}
{-# COMPILED readBinaryFileLazy 
    ( Data.ByteString.Lazy.readFile
    . Data.Text.unpack
    )
#-}
{-# COMPILED writeBinaryFileLazy
    ( Data.ByteString.Lazy.writeFile
    . Data.Text.unpack
    )
#-}
{-# COMPILED Colist←Lazy
    ( Data.ByteString.Lazy.unpack ) #-}
{-# COMPILED Colist→Lazy
    ( Data.ByteString.Lazy.pack ) #-}
{-# COMPILED emptyLazy (Data.ByteString.Lazy.empty) #-}
{-# COMPILED lengthLazy (Data.ByteString.Lazy.length) #-}

postulate
  ByteStringStrict : Set
  readBinaryFileStrict    : String → IO ByteStringStrict
  writeBinaryFileStrict   : String → ByteStringStrict → IO Unit
  List←Strict : ByteStringStrict → List Word8
  List→Strict : List Word8 → ByteStringStrict
  emptyStrict : ByteStringStrict
  lengthStrict : ByteStringStrict → Int

{-# COMPILED_TYPE ByteStringStrict 
    Data.ByteString.ByteString
#-}
{-# COMPILED readBinaryFileStrict 
    ( Data.ByteString.readFile
    . Data.Text.unpack
    )
#-}
{-# COMPILED writeBinaryFileStrict
    ( Data.ByteString.writeFile
    . Data.Text.unpack
    )
#-}
{-# COMPILED List←Strict
    ( Data.ByteString.unpack ) #-}
{-# COMPILED List→Strict
    ( Data.ByteString.pack ) #-}
{-# COMPILED emptyStrict (Data.ByteString.empty) #-}
{-# COMPILED lengthStrict (Data.ByteString.length) #-}


postulate
  toLazy : ByteStringStrict → ByteStringLazy
  toStrict : ByteStringLazy  → ByteStringStrict
{-# COMPILED toLazy (Data.ByteString.Lazy.fromStrict) #-}
{-# COMPILED toStrict (Data.ByteString.Lazy.toStrict) #-}

