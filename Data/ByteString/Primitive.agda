module Data.ByteString.Primitive where

open import Data.Word using (Word8)
open import Data.Nat using (ℕ)
open import Data.Colist using (Colist)
open import Data.List using (List)
open import Data.String using (String)
open import Data.Bool using (Bool)

{-# FOREIGN GHC import qualified Data.Word    #-}
{-# FOREIGN GHC import qualified Data.Text    #-}
{-# FOREIGN GHC import qualified Data.ByteString.Lazy    #-}
{-# FOREIGN GHC import qualified Data.ByteString    #-}
open import IO.Primitive using (IO)
open import Foreign.Haskell using (Unit)

{-# FOREIGN GHC import qualified Data.Int #-}
postulate
  Int : Set
  Int64 : Set
  intToℕ : Int → ℕ
  int64Toℕ : Int64 → ℕ
{-# COMPILE GHC Int = type (Prelude.Int) #-}
{-# COMPILE GHC Int64 = type (Data.Int.Int64) #-}
{-# COMPILE GHC intToℕ = (Prelude.fromIntegral) #-}
{-# COMPILE GHC int64Toℕ = (Prelude.fromIntegral) #-}

postulate
  ByteStringLazy : Set
  readBinaryFileLazy    : String → IO ByteStringLazy
  writeBinaryFileLazy   : String → ByteStringLazy → IO Unit
  Colist←Lazy : ByteStringLazy → Colist Word8
  Colist→Lazy : Colist Word8 → ByteStringLazy
  emptyLazy : ByteStringLazy
  lengthLazy : ByteStringLazy → Int64

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
{-# COMPILE GHC lengthLazy = (Data.ByteString.Lazy.length) #-}

postulate
  ByteStringStrict : Set
  readBinaryFileStrict    : String → IO ByteStringStrict
  writeBinaryFileStrict   : String → ByteStringStrict → IO Unit
  List←Strict : ByteStringStrict → List Word8
  List→Strict : List Word8 → ByteStringStrict
  emptyStrict : ByteStringStrict
  lengthStrict : ByteStringStrict → Int

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
{-# COMPILE GHC lengthStrict = (Data.ByteString.length) #-}


postulate
  toLazy : ByteStringStrict → ByteStringLazy
  toStrict : ByteStringLazy  → ByteStringStrict
  lazy≟lazy : ByteStringLazy → ByteStringLazy → Bool
  strict≟strict : ByteStringStrict → ByteStringStrict → Bool
{-# COMPILE GHC toLazy = (Data.ByteString.Lazy.fromStrict) #-}
{-# COMPILE GHC toStrict = (Data.ByteString.Lazy.toStrict) #-}
{-# COMPILE GHC lazy≟lazy = (==) #-}
{-# COMPILE GHC strict≟strict = (==) #-}

lazy≟strict : ByteStringLazy → ByteStringStrict → Bool
lazy≟strict l s = lazy≟lazy l (toLazy s)
strict≟lazy : ByteStringStrict → ByteStringLazy → Bool
strict≟lazy s l = lazy≟lazy (toLazy s) l

