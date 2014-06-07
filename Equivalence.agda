module Equivalence where

open import Relation

record Equivalence {i} {A : Set i} (R : Rel A A) : Set i where
  field
    refl : ∀ {x} → R x x
    !_ : ∀ {x y} → R x y → R y x
    _∙_ : ∀ {x y z} → R y z → R x y → R x z

  infixr 9 _∙_
