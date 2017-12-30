{-# OPTIONS --without-K #-}

module Data.ByteString.Primitive where

open import Data.Word8 using (Word8)
open import Data.Nat using (ℕ; _<_)
open import Data.Colist using (Colist)
open import Data.List using (List; length)
open import Data.String using (String)
open import Data.Bool using (Bool)
open import Data.Product using (_×_)
open import Data.Tuple using (Pair)

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

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
  IntToℕ : Int → ℕ
  ℕToInt : ℕ → Int
  int64Toℕ : Int64 → ℕ
  ℕToInt64 : ℕ → Int64
{-# COMPILE GHC Int = type (Prelude.Int) #-}
{-# COMPILE GHC Int64 = type (Data.Int.Int64) #-}
{-# COMPILE GHC IntToℕ = (Prelude.fromIntegral) #-}
{-# COMPILE GHC ℕToInt = (Prelude.fromIntegral) #-}
{-# COMPILE GHC int64Toℕ = (Prelude.fromIntegral) #-}
{-# COMPILE GHC ℕToInt64 = (Prelude.fromIntegral) #-}

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

-- properties
module _ where
  List→Strict→List : (l : List Word8) → List←Strict (List→Strict l) ≡ l
  List→Strict→List l = trustMe

  Strict→List→Strict : (bs : ByteStringStrict) → List→Strict (List←Strict bs) ≡ bs
  Strict→List→Strict bs = trustMe

  ∣Strict∣≡∣List∣ : (bs : ByteStringStrict) → IntToℕ (lengthStrict bs) ≡ length (List←Strict bs)
  ∣Strict∣≡∣List∣ bs = trustMe

  2³¹ = 2147483648
  ∣List∣≡∣Strict∣ : (l : List Word8) → (l-small : length l < 2³¹) → IntToℕ (lengthStrict (List→Strict l)) ≡ length l
  ∣List∣≡∣Strict∣ l l-small = trustMe

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

postulate
  fromChunks : List ByteStringStrict → ByteStringLazy
  toChunks : ByteStringLazy → List ByteStringStrict
{-# COMPILE GHC fromChunks = (Data.ByteString.Lazy.fromChunks) #-}
{-# COMPILE GHC toChunks = (Data.ByteString.Lazy.toChunks) #-}


