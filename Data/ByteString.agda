import Data.ByteString.Primitive as Prim

module Data.ByteString where

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

