module Policies where

open import Relation.Binary

record DecSecurityPolicy : Set₁ where
  field
    SD : Set
    _↝_ : SD → SD → Set
    _↝?_ : Decidable _↝_
