module Relation where

open import Agda.Primitive

Rel : {i j k : Level} → Set i → Set j → Set (i ⊔ j ⊔ lsuc k)
Rel {k = k} A B = A → B → Set k

