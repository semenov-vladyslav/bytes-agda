module Data.Word.Primitive where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.Nat using (Nat; _<_)
open import Agda.Builtin.FromNat using (Number)


{-# IMPORT Data.Word #-}
postulate
  Word8 : Set
  _==_ : Word8 → Word8 → Bool
  _xor_ : Word8 → Word8 → Word8
  _and_ : Word8 → Word8 → Word8
  _or_ : Word8 → Word8 → Word8
{-# COMPILED_TYPE Word8 Data.Word.Word8 #-}
{-# COMPILED _==_ (==) #-}
{-# COMPILED _xor_ (xor) #-}
{-# COMPILED _and_ (.&.) #-}
{-# COMPILED _or_ (.|.) #-}


instance
  Nat-Number : Number Nat
  Nat-Number = record
    { Constraint = λ _ → ⊤
    ; fromNat = λ n → n
    }

postulate
  Word8fromNat : (n : Nat) → Word8
  Word8toNat : Word8 → Nat
{-# COMPILED Word8fromNat (\n -> fromIntegral n) #-}
{-# COMPILED Word8toNat (\w -> fromIntegral w) #-}

data IsTrue : Bool → Set where
  itis : IsTrue true

instance
  indeed : IsTrue true
  indeed = itis

instance
  Word8-Number : Number Word8
  Word8-Number = record
    { Constraint = λ n → IsTrue (n < 256)
    ; fromNat = λ n → Word8fromNat n
    }

toℕ : Word8 → Nat
toℕ = Word8toNat
