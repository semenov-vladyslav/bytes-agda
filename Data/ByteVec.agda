module Data.ByteVec where

open import Data.ByteString using (ByteString; length)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_)

ByteVec : ∀ {k} → ℕ → Set
ByteVec {k} n = Σ (ByteString k) (λ bs → n ≡ length bs)
