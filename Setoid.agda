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

record Map {i j} (A : Setoid {i}) (B : Setoid {j}) : Set (i ⊔ j) where
  module A = Setoid A
  module B = Setoid B
  field
    _$_ :  A.T → B.T
    ext : {x y : A.T} → x A.~ y → _$_ x B.~ _$_ y
open Map public using (_$_)

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
