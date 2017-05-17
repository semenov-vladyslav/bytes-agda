module Data.Tuple where

open import Level using (_⊔_)
import Data.Product as P

record Pair {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B
{-# FOREIGN GHC type AgdaPair a b c d = (c , d) #-}
{-# COMPILE GHC Pair = type MAlonzo.Code.Data.Tuple.AgdaPair #-}


Pair→× : ∀ {a b A B} → Pair {a} {b} A B → A P.× B
Pair→× (fst , snd) = fst P., snd

×→Pair : ∀ {a b A B} → P._×_ {a} {b} A B → Pair A B
×→Pair (fst P., snd) = fst , snd

