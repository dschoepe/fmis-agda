-- Generalized noninference:
module GNF where

open import ComputationalModels
open import Data.Bool
open import Data.List
open import Data.Nat hiding (_≟_)
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Level
open import Policies
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module GNFProp
  (ES : EventSystem {Level.zero})
  (dom : EventSystem.E ES → HL) where

  _×?_ : {A B : Set} → Dec A → Dec B → Dec (A × B)
  yes p ×? yes p₁ = yes (p , p₁)
  yes p ×? no ¬p = no (λ z → ¬p (proj₂ z))
  no ¬p ×? b = no (λ z → ¬p (proj₁ z))

  open EventSystem ES
  open DecSecurityPolicy HLPolicy

  Ld : (e : E) → Dec (dom e ≡ L)
  Ld e = dom e ≟ᵈ L

  HId : (e : E) → Dec (dom e ≡ H × (I e ≡ true))
  HId e = (dom e ≟ᵈ H) ×? (I e ≟ true)

  gnf : Set
  gnf = ∀ {τ} → Tr τ → ∃ (λ τ' → Tr τ' × τ ↾ Ld ≡ τ' ↾ Ld × τ' ↾ HId ≡ [])

module PipeDownInsecure where
  open import ExampleSystems

  open PipeDown
  open GNFProp pipe-down dom
  open EventSystem pipe-down

  insecure : ¬ gnf
  insecure sec with sec {hi 13 ∷ lo 13 ∷ []} ([] , add-hi-lo 13 empty)
  insecure sec | [] , (proj₂ , proj₃) , () , proj₅
  insecure sec | hi x ∷ proj₁ , (proj₂ , proj₃) , proj₄ , ()
  insecure sec | lo x ∷ proj₁ , (proj₂ , ()) , proj₄ , proj₅

module PipeUpSecure where
  open import ExampleSystems

  open PipeUp
  open GNFProp pipe-up dom
  open EventSystem pipe-up

  lemma : ∀ τ → τ ↾ HId ≡ []
  lemma [] = refl
  lemma (li _ ∷ τ) = lemma τ
  lemma (ho _ ∷ τ) = lemma τ

  secure : gnf
  secure {τ} tr = τ , tr , refl , lemma τ
