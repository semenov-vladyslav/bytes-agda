{-# OPTIONS --without-K #-}

module Data.Tuple.Base where

open import Level using (_⊔_)

-- non-dependent pair; failed to reuse _×_
record Pair {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B
{-# FOREIGN GHC type AgdaPair a b c d = (c , d) #-}
-- {-# COMPILE GHC Pair = type MAlonzo.Code.Data.Tuple.AgdaPair #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Data.Tuple.AgdaPair ((,)) #-}

infixl 5 _∥_

_∥_ = Pair
