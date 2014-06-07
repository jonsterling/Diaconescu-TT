module Equality where

data _==_ {i} {A : Set i} (x : A) : A → Set i where
  idp : x == x
  
