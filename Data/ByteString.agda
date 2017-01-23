module Data.ByteString where

import Data.ByteString.Primitive as Prim

open import Data.Word using (Word8)
open import Data.Nat using (ℕ)
open import Data.Colist using (Colist)
open import Data.List using (List)
open import Data.String using (String)


data ByteStringKind : Set where
  Lazy Strict : ByteStringKind

ByteString : ByteStringKind → Set
ByteString Lazy = Prim.ByteStringLazy
ByteString Strict = Prim.ByteStringStrict

empty : ∀ {k} → ByteString k
empty {Lazy} = Prim.emptyLazy
empty {Strict} = Prim.emptyStrict

length : ∀ {k} → ByteString k → ℕ
length {Lazy} = Prim.lengthLazy
length {Strict} = Prim.lengthStrict

ByteStringRep : ByteStringKind → Set
ByteStringRep Lazy = Colist Word8
ByteStringRep Strict = List Word8

toRep : ∀ {k} → ByteString k → ByteStringRep k
toRep {Lazy} = Prim.Colist←Lazy
toRep {Strict} = Prim.List←Strict

fromRep : ∀ {k} → ByteStringRep k → ByteString k
fromRep {Lazy} = Prim.Colist→Lazy
fromRep {Strict} = Prim.List→Strict

