import Data.ByteString.Primitive as Prim
import Data.ByteString.Utf8 as Utf8

module Data.ByteString where

open import Data.Word using (Word8)
open import Data.Nat using (ℕ)
open import Data.Colist using (Colist)
open import Data.List using (List)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)


data ByteStringKind : Set where
  Lazy Strict : ByteStringKind

ByteString : ByteStringKind → Set
ByteString Lazy = Prim.ByteStringLazy
ByteString Strict = Prim.ByteStringStrict

empty : ∀ {k} → ByteString k
empty {Lazy} = Prim.emptyLazy
empty {Strict} = Prim.emptyStrict

length : ∀ {k} → ByteString k → ℕ
length {Lazy} bs = Prim.int64Toℕ (Prim.lengthLazy bs)
length {Strict} bs = Prim.intToℕ (Prim.lengthStrict bs)

ByteStringRep : ByteStringKind → Set
ByteStringRep Lazy = Colist Word8
ByteStringRep Strict = List Word8

unpack : ∀ {k} → ByteString k → ByteStringRep k
unpack {Lazy} = Prim.Colist←Lazy
unpack {Strict} = Prim.List←Strict

pack : ∀ {k} → ByteStringRep k → ByteString k
pack {Lazy} = Prim.Colist→Lazy
pack {Strict} = Prim.List→Strict


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

