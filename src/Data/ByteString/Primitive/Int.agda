{-# OPTIONS --without-K #-}

module Data.ByteString.Primitive.Int where

open import Agda.Builtin.Nat using (Nat)

{-# FOREIGN GHC import qualified Data.Int #-}
postulate
  Int : Set
  Int64 : Set
  IntToℕ : Int → Nat
  ℕToInt : Nat → Int
  int64Toℕ : Int64 → Nat
  ℕToInt64 : Nat → Int64
{-# COMPILE GHC Int = type (Prelude.Int) #-}
{-# COMPILE GHC Int64 = type (Data.Int.Int64) #-}
{-# COMPILE GHC IntToℕ = (Prelude.fromIntegral) #-}
{-# COMPILE GHC ℕToInt = (Prelude.fromIntegral) #-}
{-# COMPILE GHC int64Toℕ = (Prelude.fromIntegral) #-}
{-# COMPILE GHC ℕToInt64 = (Prelude.fromIntegral) #-}
