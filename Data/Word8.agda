{-# OPTIONS --without-K #-}

module Data.Word8 where

open import Data.Word8.Primitive public

open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Nullary using (yes; no)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)


infix 4 _≟_

_≟_ : Decidable {A = Word8} _≡_
w₁ ≟ w₂ with w₁ == w₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

-- toℕ : Word8 → Nat
-- toℕ = primWord8toNat
