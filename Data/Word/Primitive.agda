module Data.Word.Primitive where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)


{-# IMPORT Data.Word #-}
{-# IMPORT Data.Bits #-}
postulate
  Word8 : Set
  _==_ : Word8 → Word8 → Bool
  _xor_ : Word8 → Word8 → Word8
  _and_ : Word8 → Word8 → Word8
  _or_ : Word8 → Word8 → Word8
{-# COMPILED_TYPE Word8 Data.Word.Word8 #-}
{-# COMPILED _==_ (Prelude.==) #-}
{-# COMPILED _xor_ (Data.Bits.xor) #-}
{-# COMPILED _and_ (Data.Bits..&.) #-}
{-# COMPILED _or_ (Data.Bits..|.) #-}


postulate
  Word8fromNat : (n : Nat) → Word8
  Word8toNat : Word8 → Nat
{-# COMPILED Word8fromNat (\n -> Prelude.fromIntegral n) #-}
{-# COMPILED Word8toNat (\w -> Prelude.fromIntegral w) #-}
