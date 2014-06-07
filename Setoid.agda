module Setoid where

open import Agda.Primitive

open import Equality
open import Equivalence
open import Relation

record Setoid {i} : Set (lsuc i) where
  field
    T : Set i
    _~_ : Rel T T
    equiv : Equivalence _~_

intensional-setoid : {i : Level} → Set i → Setoid {i}
intensional-setoid A =
  record { T = A
            ; _~_ = _==_
            ; equiv =
                record { refl = idp
                          ; !_ = λ { {x} {.x} idp → idp }
                          ; _∙_ = λ { {x} {y} {.y} idp q → q }
                          }
            }
