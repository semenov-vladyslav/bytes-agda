{-# OPTIONS --without-K #-}

module Data.Word8.Primitive where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)


{-# FOREIGN GHC import qualified Data.Word #-}
{-# FOREIGN GHC import qualified Data.Bits #-}
postulate
  Word8 : Set
  _==_ : Word8 → Word8 → Bool
  _/=_ : Word8 → Word8 → Bool
  _xor_ : Word8 → Word8 → Word8
  _and_ : Word8 → Word8 → Word8
  _or_ : Word8 → Word8 → Word8
{-# COMPILE GHC Word8 = type Data.Word.Word8 #-}
{-# COMPILE GHC _==_ = (Prelude.==) #-}
{-# COMPILE GHC _/=_ = (Prelude./=) #-}
{-# COMPILE GHC _xor_ = (Data.Bits.xor) #-}
{-# COMPILE GHC _and_ = (Data.Bits..&.) #-}
{-# COMPILE GHC _or_ = (Data.Bits..|.) #-}


postulate
  primWord8fromNat : Nat → Word8
  primWord8toNat : Word8 → Nat
{-# COMPILE GHC primWord8fromNat = (\n -> Prelude.fromIntegral n) #-}
{-# COMPILE GHC primWord8toNat = (\w -> Prelude.fromIntegral w) #-}
