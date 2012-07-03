module ExampleSystems where

open import ComputationalModels
open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Empty
open import Data.Product
open import Data.Unit
open import Relation.Nullary

module PipeDown where

  data E : Set where
    hi : ℕ → E
    lo : ℕ → E

  private
    O : E → Bool
    O (hi x) = false
    O (lo x) = true

    I : E → Bool
    I (hi x) = true
    I (lo x) = false

    disj : bools-disjoint I O
    disj (hi x) = (λ x₁ x₂ → x₂) , (λ x₁ x₂ → x₁)
    disj (lo x) = (λ x₁ x₂ → x₁) , (λ x₁ x₂ → x₂)

  data Tr' : List E → Set where
    empty : Tr' []
    add-hi-lo : ∀ {xs} n → Tr' xs → Tr' (hi n ∷ lo n ∷ xs)

  pipe-down : EventSystem
  pipe-down = record
              { E = E
              ; I = I
              ; O = O
              ; I-O-disjoint = disj
              ; Tr = ↓ Tr' ↓
              ; prefix-closed = ↓-correct Tr'
              }

  open import Policies
  dom : E → HL
  dom (hi _) = H
  dom (lo _) = L

module PipeUp where
  data E : Set where
    li : ℕ → E
    ho : ℕ → E

  private
    O : E → Bool
    O (li x) = false
    O (ho x) = true

    I : E → Bool
    I (li x) = true
    I (ho x) = false

    disj : bools-disjoint I O
    disj (li x) = (λ x₁ x₂ → x₂) , (λ x₁ x₂ → x₁)
    disj (ho x) = (λ x₁ x₂ → x₁) , (λ x₁ x₂ → x₂)

  data Tr' : List E → Set where
    empty : Tr' []
    add-li-ho : ∀ {xs} n → Tr' xs → Tr' (li n ∷ ho n ∷ xs)

  pipe-up : EventSystem
  pipe-up = record
          { E = E
          ; I = I
          ; O = O
          ; I-O-disjoint = disj
          ; Tr = ↓ Tr' ↓
          ; prefix-closed = ↓-correct Tr'
          }

  open import Policies
  dom : E → HL
  dom (li _) = L
  dom (ho _) = H
