{-# OPTIONS --without-K #-}

module Data.ByteVec where

import Data.ByteString as BS
open import Data.Word8 using (Word8)
open BS using (ByteString; length)
open import Data.Nat using (ℕ; _≟_; _<_)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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

{-
infix 4 _≟_

_≟_ : ∀ {k} → Decidable {A = ByteString k} _≡_
_≟_ {Lazy} s₁ s₂ with Prim.lazy≟lazy s₁ s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _
_≟_ {Strict} s₁ s₂ with Prim.strict≟strict s₁ s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

-- behind _==_ is the same idea as in Data.String
infix 4 _==_

_==_ : ∀ {k} → ByteString k → ByteString k → Bool
_==_ {k} s₁ s₂ = ⌊ s₁ ≟ s₂ ⌋
-}

