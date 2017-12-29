{-# OPTIONS --without-K #-}

module Data.ByteString where

import Data.ByteString.Primitive as Prim
import Data.ByteString.Utf8 as Utf8

open import Data.Word8 using (Word8)
open import Data.Nat using (ℕ)
open import Data.Colist using (Colist)
open import Data.List using (List)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_)
open import Data.Tuple using (Pair→×)

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

null : ∀ {k} → ByteString k → Bool
null {Lazy} = Prim.nullLazy
null {Strict} = Prim.nullStrict

length : ∀ {k} → ByteString k → ℕ
length {Lazy} bs = Prim.int64Toℕ (Prim.lengthLazy bs)
length {Strict} bs = Prim.IntToℕ (Prim.lengthStrict bs)

unsafeHead : ∀ {k} → ByteString k → Word8
unsafeHead {Lazy} = Prim.headLazy
unsafeHead {Strict} = Prim.headStrict

unsafeTail : ∀ {k} → ByteString k → ByteString k
unsafeTail {Lazy} = Prim.tailLazy
unsafeTail {Strict} = Prim.tailStrict

unsafeIndex : ∀ {k} → ByteString k → ℕ → Word8
unsafeIndex {Lazy} bs ix = Prim.indexLazy bs (Prim.ℕToInt ix)
unsafeIndex {Strict} bs ix = Prim.indexStrict bs (Prim.ℕToInt ix)

unsafeSplitAt : ∀ {k} → ByteString k → ℕ → (ByteString k) × (ByteString k)
unsafeSplitAt {Lazy} bs ix = Pair→× (Prim.splitAtLazy bs (Prim.ℕToInt ix))
unsafeSplitAt {Strict} bs ix = Pair→× (Prim.splitAtStrict bs (Prim.ℕToInt ix))

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

_++_ : ByteString Lazy → ByteString Lazy → ByteString Lazy
_++_ = Prim.appendLazy

fromChunks : List (ByteString Strict) → ByteString Lazy
fromChunks = Prim.fromChunks

toChunks : ByteString Lazy → List (ByteString Strict)
toChunks = Prim.toChunks

toLazy : ByteString Strict → ByteString Lazy
toLazy = Prim.toLazy

toStrict : ByteString Lazy → ByteString Strict
toStrict = Prim.toStrict

