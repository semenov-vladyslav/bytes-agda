{-
This module imports `Agda.Builtin.FromNat` which enables natural literals overloading.
Import this module as follows:
`open import Data.Word as W using (Nat-Number)`
-}
module Data.Word where

open import Data.Word.Primitive public

open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Nullary using (yes; no)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

-- Decidable equality copy-pasted from Data.String

infix 4 _≟_

_≟_ : Decidable {A = Word8} _≡_
w₁ ≟ w₂ with w₁ == w₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

-- toℕ : Word8 → Nat
-- toℕ = Word8toNat
