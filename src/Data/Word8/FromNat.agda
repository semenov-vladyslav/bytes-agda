{-# OPTIONS --without-K #-}

module Data.Word8.FromNat where

open import Data.Word8.Primitive
-- open import Agda.Builtin.Bool using (Bool; true)
-- open import Agda.Builtin.Nat using (Nat; _<_)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.FromNat using (Number)


{-
instance
  NumberNat : Number Nat
  NumberNat = record
    { Constraint = λ _ → ⊤
    ; fromNat = λ n → n
    }

data IsTrue : Bool → Set where
  itis : IsTrue true

instance
  indeed : IsTrue true
  indeed = itis
-}

instance
  NumberWord8 : Number Word8
  NumberWord8 = record
    { Constraint = λ n → ⊤ -- IsTrue (n < 256)
    ; fromNat = λ n → primWord8fromNat n
    }

