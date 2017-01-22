module Data.Word.FromNat where

import Data.Fin as F
open import Data.Word.Primitive
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat; _<_)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.FromNat using (Number)


instance
  Nat-Number : Number Nat
  Nat-Number = record
    { Constraint = λ _ → ⊤
    ; fromNat = λ n → n
    }

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

