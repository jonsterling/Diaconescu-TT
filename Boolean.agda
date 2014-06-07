module Boolean where

open import Agda.Primitive
open import Equality
open import Coproduct
open import Empty

data Boolean {i} : Set i where
  tt ff : Boolean

_≟_ : {i : Level} (a b : Boolean {i}) → (a == b) + ¬ (a == b)
tt ≟ tt = inl idp
tt ≟ ff = inr (λ ())
ff ≟ tt = inr (λ ())
ff ≟ ff = inl idp

