module Policies where

open import Data.Unit
open import Data.Empty
open import Level
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

record DecSecurityPolicy {ℓ} : Set (Level.suc ℓ)  where
  field
    SD : Set ℓ
    _↝_ : SD → SD → Set ℓ
    _↝?_ : Decidable _↝_
    _≟ᵈ_ : Decidable (_≡_ {A = SD})

data HL : Set where
    L : HL
    H : HL

_↝ʰ_ : HL → HL → Set
L ↝ʰ _ = ⊤
H ↝ʰ H = ⊤
H ↝ʰ _ = ⊥

_↝ʰ?_ : Decidable (_↝ʰ_)
L ↝ʰ? d' = yes tt
H ↝ʰ? L = no (λ z → z)
H ↝ʰ? H = yes tt

_≟ʰ_ : Decidable (_≡_ {A = HL})
L ≟ʰ L = yes refl
L ≟ʰ H = no (λ ())
H ≟ʰ L = no (λ ())
H ≟ʰ H = yes refl

HLPolicy : DecSecurityPolicy
HLPolicy = record { SD = HL; _↝_ = _↝ʰ_; _↝?_ = _↝ʰ?_ ; _≟ᵈ_ = _≟ʰ_ }
