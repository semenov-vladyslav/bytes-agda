module Data.ByteString where

open import Data.Word using (Word8)
open import Data.Colist using (Colist)
open import Data.List using (List)
open import Data.String using (String)


{-# IMPORT Data.Text    #-}
{-# IMPORT Data.ByteString.Lazy    #-}
{-# IMPORT Data.ByteString    #-}
module Prim where
  open import IO.Primitive using (IO)
  open import Foreign.Haskell using (Unit)

  postulate
    ByteStringLazy : Set
    readBinaryFileLazy    : String → IO ByteStringLazy
    writeBinaryFileLazy   : String → ByteStringLazy → IO Unit
    lazyToColist : ByteStringLazy → Colist Word8
    lazyFromColist : Colist Word8 → ByteStringLazy

  {-# COMPILED_TYPE ByteStringLazy 
      Data.ByteString.Lazy.ByteString
  #-}
  {-# COMPILED readBinaryFileLazy 
      ( Data.ByteString.Lazy.readFile
      . Data.Text.unpack
      )
  #-}
  {-# COMPILED writeBinaryFileLazy
      ( Data.ByteString.Lazy.writeFile
      . Data.Text.unpack
      )
  #-}
  {-# COMPILED lazyToColist
      ( Data.ByteString.Lazy.unpack ) #-}
  {-# COMPILED lazyFromColist
      ( Data.ByteString.Lazy.pack ) #-}

  postulate
    ByteStringStrict : Set
    readBinaryFileStrict    : String → IO ByteStringStrict
    writeBinaryFileStrict   : String → ByteStringStrict → IO Unit
    strictToList : ByteStringStrict → List Word8
    strictFromList : List Word8 → ByteStringStrict

  {-# COMPILED_TYPE ByteStringStrict 
      Data.ByteString.ByteString
  #-}
  {-# COMPILED readBinaryFileStrict 
      ( Data.ByteString.readFile
      . Data.Text.unpack
      )
  #-}
  {-# COMPILED writeBinaryFileStrict
      ( Data.ByteString.writeFile
      . Data.Text.unpack
      )
  #-}
  {-# COMPILED strictToList
      ( Data.ByteString.unpack ) #-}
  {-# COMPILED strictFromList
      ( Data.ByteString.pack ) #-}

  postulate
    readBinaryFile    : String → IO (Colist Word8)
    writeBinaryFile   : String → Colist Word8 → IO Unit
  {-# COMPILED readBinaryFile       (fmap Data.ByteString.Lazy.unpack . Data.ByteString.Lazy.readFile . Data.Text.unpack)           #-}
  {-# COMPILED writeBinaryFile      (\fn -> Data.ByteString.Lazy.writeFile (Data.Text.unpack fn) . Data.ByteString.Lazy.pack) #-}


data ByteStringKind : Set where
  Lazy Strict : ByteStringKind

ByteString : ByteStringKind → Set
ByteString Lazy = Prim.ByteStringLazy
ByteString Strict = Prim.ByteStringStrict

ByteStringRep : ByteStringKind → Set
ByteStringRep Lazy = Colist Word8
ByteStringRep Strict = List Word8

toRep : ∀ {k} → ByteString k → ByteStringRep k
toRep {Lazy} = Prim.lazyToColist
toRep {Strict} = Prim.strictToList

fromRep : ∀ {k} → ByteStringRep k → ByteString k
fromRep {Lazy} = Prim.lazyFromColist
fromRep {Strict} = Prim.strictFromList

module IO where
  open import IO using (IO; _>>_; _>>=_; lift; return)
  open import Data.Unit using (⊤)
  open import Coinduction using (♯_)

  readBinaryFile : ∀ {k} → String → IO (ByteString k)
  readBinaryFile {Lazy} f = lift (Prim.readBinaryFileLazy f)
  readBinaryFile {Strict} f = lift (Prim.readBinaryFileStrict f)

  readBinaryFile′ : ∀ {k} → String → IO (ByteStringRep k)
  readBinaryFile′ {k} f = ♯ readBinaryFile f >>= (λ bs → ♯ return (toRep bs))

  writeBinaryFile : ∀ {k} → String → ByteString k → IO ⊤
  writeBinaryFile {Lazy} f s =
    ♯ lift (Prim.writeBinaryFileLazy f s) >>
    ♯ return _
  writeBinaryFile {Strict} f s =
    ♯ lift (Prim.writeBinaryFileStrict f s) >>
    ♯ return _

  writeBinaryFile′ : ∀ {k} → String → ByteStringRep k → IO ⊤
  writeBinaryFile′ {k} f bs = writeBinaryFile f (fromRep bs)

