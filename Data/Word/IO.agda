module Data.Word.IO where

open import Data.Word using (Word8)
open import Data.Colist using (Colist)
open import Data.String using (String)


{-# IMPORT Data.Text    #-}
{-# IMPORT Data.ByteString.Lazy    #-}
module Prim where
  open import IO.Primitive using (IO)
  open import Foreign.Haskell using (Unit)

  postulate
    readBinaryFile    : String → IO (Colist Word8)
    writeBinaryFile   : String → Colist Word8 → IO Unit
  {-# COMPILED readBinaryFile       (fmap Data.ByteString.Lazy.unpack . Data.ByteString.Lazy.readFile . Data.Text.unpack)           #-}
  {-# COMPILED writeBinaryFile      (\fn -> Data.ByteString.Lazy.writeFile (Data.Text.unpack fn) . Data.ByteString.Lazy.pack) #-}


open import IO using (IO; _>>_; lift; return)
open import Data.Unit using (⊤)
open import Coinduction using (♯_)

readBinaryFile : String → IO (Colist Word8)
readBinaryFile f = lift (Prim.readBinaryFile f)

writeBinaryFile : String → (Colist Word8) → IO ⊤
writeBinaryFile f s =
  ♯ lift (Prim.writeBinaryFile f s) >>
  ♯ return _
