module Diaconescu where

open import Agda.Primitive

open import Boolean
open import Coproduct
open import Product
open import Empty
open import Equality
open import Equivalence
open import Function
open import Relation
open import Setoid

module _ {i j} {I : Setoid {i}} {S : Setoid {j}} where
  module I = Setoid.Setoid I 
  module S = Setoid.Setoid S 
  open Setoid.Setoid {{...}}

  -- Ext is a predicate on functions between setoids that they respect
  -- the equivalence relations
  Ext : (I.T → S.T) → Set (i ⊔ j)
  Ext f = ∀ {a b} → a ~ b → f a ~ f b

  -- ExtAC is Martin-Löf's "Extensional Axiom of Choice", which is not justified
  -- in Constructive Type Theory.
  postulate
    ExtAC : {k : Level} (A[_] : Rel {k = k} I.T S.T)
               → (∀ i → Σ S.T A[ i ])
               → Σ[ f ∶ (I.T → S.T) ] (Ext f × (∀ {i} → A[ i ] (f i)))

-- Given ExtAC, we have the Law of the Excluded Middle: every type is decidable
-- The reasoning in this proof is largely derived from Danko Ilik's "Zermelo's Well-Ordering
-- Theorem in Type Theory" (http://www.lix.polytechnique.fr/~danko/wott.pdf)
LEM : {i : Level} (P : Set i) → P + ¬ P
LEM P = decide-P
  where
    Nice : Setoid
    Nice = intensional-setoid Boolean

    Naughty : Setoid 
    Naughty = record { T = Boolean
                             ; _~_ = λ x y → (x == y) + P
                             ; equiv =
                                 record { refl = inl idp
                                           ; !_ = λ { {x} {.x} (inl idp) → inl idp ; (inr p) → inr p }
                                           ; _∙_ = λ { {x} {y} {.y} (inl idp) q → q ; (inr x) q → inr x }
                                           }
                             }

    open Setoid.Setoid {{...}}
    
    [f] : Σ[ f ∶ (Boolean → Boolean) ] (∀ {x y} → x ~ y → f x ~ f y) × (∀ {x} → x ~ f x)
    [f] = ExtAC {I = Naughty} {S = Nice} _~_ (λ i → i , inl idp) 

    decide-P : P + ¬ P
    decide-P with f tt ≟ f ff
      where f = π₁ [f] 
    decide-P | inl q with ! f-rel ∙ R-resp q ∙ f-rel
      where
        open Equivalence.Equivalence equiv
        f-rel = π₂ (π₂ [f])
        R-resp : ∀ {a b} → a == b → a ~ b
        R-resp idp = inl idp
    decide-P | inl q | inl ()
    decide-P | inl _ | inr p = inl p
    decide-P | inr q = inr (q ∘ (π₁ (π₂ [f])) ∘ inr)
