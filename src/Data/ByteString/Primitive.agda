{-# OPTIONS --without-K #-}

module Data.ByteString.Primitive where

open import Data.Word8.Primitive using (Word8)
open import Data.Nat using (ℕ; _<_)
open import Data.Colist using (Colist)
open import Data.List using (List; length)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.IO using (IO)
open import Data.Tuple.Base using (Pair)

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

{-# FOREIGN GHC import qualified Data.ByteString.Lazy    #-}
open import Data.ByteString.Primitive.Int
open import Data.ByteString.Primitive.Lazy
open import Data.ByteString.Primitive.Strict

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


