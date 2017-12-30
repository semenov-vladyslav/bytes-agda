{-# OPTIONS --without-K #-}

module Data.ByteVec where

import Data.ByteString as BS
open import Data.Word8 using (Word8)
open BS using (ByteString; length)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

open BS public using (ByteStringKind; Lazy; Strict)

ByteVec : ∀ {k} → ℕ → Set
ByteVec {k} n = Σ (ByteString k) (λ bs → n ≡ length bs)

mkVec′ : ∀ {k} → (bs : ByteString k) → ByteVec {k} (length bs)
mkVec′ {k} bs = bs , refl

mkVec : ∀ {k} (n : ℕ) (bs : ByteString k)
  → (n≡∣bs∣ : n ≡ length bs)
  → ByteVec {k} n
mkVec {k} n = _,_

primMkVec : ∀ {k n} → ByteString k → ByteVec {k} n
primMkVec bs = bs , trustMe

index : ∀ {k n} → ByteVec {k} n → (ix : ℕ) → {ix<n : ix < n} → Word8
index (bs , _) ix {_} = BS.unsafeIndex bs ix

module test where
  open import Data.ByteString.Utf8 using (packStrict)
  -- bv5 : ByteVec {_} 5
  -- bv5 = packStrict "asdef" Σ., {!!}
  bv′ : _
  bv′ = mkVec′ (packStrict "asdef")

infix 4 _≟_

private
  t : ∀ {n k} → {v : ByteString k} → (us vs : n ≡ length v) → us ≡ vs
  t us vs = trustMe -- only one proof: refl

_≟_ : ∀ {k n} → Decidable {A = ByteVec {k} n} _≡_
_≟_ {n = n} (u , us) (v , vs) with u BS.≟ v
_≟_ {n = n} (u , us) (v , vs) | yes p rewrite p | t us vs = yes refl
_≟_ {n = n} (u , us) (v , vs) | no ¬p = no (λ x → ¬p (cong proj₁ x))

