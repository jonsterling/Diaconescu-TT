module Empty where

open import Agda.Primitive

data ⊥ {i} : Set i where
¬_ : {i : Level} → Set i → Set i
¬_ {i} A = A → ⊥ {i}
