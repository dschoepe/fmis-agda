open import ComputationalModels
open import Data.List
open import Data.Nat
open import Data.Product
open import Level
open import Policies
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module Noninference where

module NoninferenceProp
  (ES : EventSystem {Level.zero})
  (dom : EventSystem.E ES → HL) where

  open EventSystem ES
  open DecSecurityPolicy HLPolicy
  noninferent : Set
  noninferent = ∀ {τ} → Tr τ → Tr (τ ↾ (λ e → dom e ≟ᵈ L))

module PipeDownInsecure  where
  open import ExampleSystems

  open PipeDown
  open NoninferenceProp pipe-down dom
  open EventSystem pipe-down

  private
    test : Tr (hi 13 ∷ lo 13 ∷ [])
    test = [] , add-hi-lo 13 empty

    test₂ : ¬ (Tr (lo 13 ∷ []))
    test₂ (_ , ())

  pipe-down-insecure : ¬ noninferent
  pipe-down-insecure ni = test₂ (ni {hi 13 ∷ lo 13 ∷ []} test)

module PipeUpInsecure where
  open import ExampleSystems

  open PipeUp
  open NoninferenceProp pipe-up dom
  open EventSystem pipe-up

  private
    test : Tr (li 13 ∷ ho 13 ∷ li 13 ∷ [])
    test = ho 13 ∷ [] , add-li-ho 13 (add-li-ho 13 empty)

    test₂ : ¬ (Tr (li 13 ∷ li 13 ∷ []))
    test₂ (_ , ())

  pipe-up-insecure : ¬ noninferent
  pipe-up-insecure ni = test₂ (ni {li 13 ∷ ho 13 ∷ li 13 ∷ []} test)
