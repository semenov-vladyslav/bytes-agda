{-# OPTIONS --without-K #-}

module Data.Tuple where

open import Data.Tuple.Base public
import Data.Product as P

Pair→× : ∀ {a b A B} → Pair {a} {b} A B → A P.× B
Pair→× (fst , snd) = fst P., snd

×→Pair : ∀ {a b A B} → P._×_ {a} {b} A B → Pair A B
×→Pair (fst P., snd) = fst , snd

