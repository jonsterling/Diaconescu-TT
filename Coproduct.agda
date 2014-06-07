module Coproduct where

open import Agda.Primitive

data _+_ {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  inl : A → A + B
  inr : B → A + B
