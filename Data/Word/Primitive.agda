module Data.Word.Primitive where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)


{-# IMPORT Data.Word #-}
postulate
  Word8 : Set
  _==_ : Word8 → Word8 → Bool
  _xor_ : Word8 → Word8 → Word8
  _and_ : Word8 → Word8 → Word8
  _or_ : Word8 → Word8 → Word8
{-# COMPILED_TYPE Word8 Data.Word.Word8 #-}
{-# COMPILED _==_ (==) #-}
{-# COMPILED _xor_ (xor) #-}
{-# COMPILED _and_ (.&.) #-}
{-# COMPILED _or_ (.|.) #-}


postulate
  Word8fromNat : (n : Nat) → Word8
  Word8toNat : Word8 → Nat
{-# COMPILED Word8fromNat (\n -> fromIntegral n) #-}
{-# COMPILED Word8toNat (\w -> fromIntegral w) #-}

toℕ : Word8 → Nat
toℕ = Word8toNat
