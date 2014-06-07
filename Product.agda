module Product where

open import Agda.Primitive

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁
open Σ public

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B 

_×_ : {i j : Level} (A : Set i) (B : Set j) → Set (i ⊔ j)
A × B = Σ A λ _ → B
