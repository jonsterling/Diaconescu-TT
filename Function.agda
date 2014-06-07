module Function where

open import Agda.Primitive

_∘_ : {i j k : Level} {A : Set i} {B : A -> Set j} {C : (x : A) → B x -> Set k} (f : {x : A} (y : B x) → C x y) (g : (x : A) → B x) (x : A) → C x (g x)
(f ∘ g) x = f (g x)
infixr 9 _∘_
