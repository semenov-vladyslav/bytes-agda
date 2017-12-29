{-# OPTIONS --without-K #-}

module Data.ByteString.IO where

import Data.ByteString.Primitive as Prim
open import Data.ByteString

open import Data.Word8 using (Word8)
open import Data.Nat using (ℕ)
open import Data.Colist using (Colist)
open import Data.List using (List)
open import Data.String using (String)

open import IO using (IO; _>>_; _>>=_; lift; return)
open import Data.Unit using (⊤)
open import Coinduction using (♯_)


readBinaryFile : ∀ {k} → String → IO (ByteString k)
readBinaryFile {Lazy} f = lift (Prim.readBinaryFileLazy f)
readBinaryFile {Strict} f = lift (Prim.readBinaryFileStrict f)

readBinaryFile′ : ∀ {k} → String → IO (ByteStringRep k)
readBinaryFile′ {k} f = ♯ readBinaryFile f >>= (λ bs → ♯ return (unpack bs))

writeBinaryFile : ∀ {k} → String → ByteString k → IO ⊤
writeBinaryFile {Lazy} f s =
  ♯ lift (Prim.writeBinaryFileLazy f s) >>
  ♯ return _
writeBinaryFile {Strict} f s =
  ♯ lift (Prim.writeBinaryFileStrict f s) >>
  ♯ return _

writeBinaryFile′ : ∀ {k} → String → ByteStringRep k → IO ⊤
writeBinaryFile′ {k} f bs = writeBinaryFile f (pack bs)


