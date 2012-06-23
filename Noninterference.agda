open import Policies
open import StateMachines

module Noninterference
  {ℓ₁ ℓ₂ ℓ₃}
  (SC : DecSecurityPolicy)
  (M : DetStateMachine {ℓ₁} {ℓ₂} {ℓ₃})
  (dom : DetStateMachine.A M → DecSecurityPolicy.SD SC) where

open DecSecurityPolicy SC
open DetStateMachine M

open import Data.Empty
open import Data.Nat hiding (_≟_)
open import Data.List
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality as PropEq
import Relation.Binary.PreorderReasoning as Pre

purge : List A → SD → List A
purge [] d = []
purge (a ∷ as) d with dom a ↝? d
purge (a ∷ as) d | yes p = a ∷ purge as d
purge (a ∷ as) d | no ¬p = purge as d

noninterferent : Set _
noninterferent = ∀ τ a → output τ a ≡ output (purge τ (dom a)) a

module Unwinding (_∼[_]_ : Σ → SD → Σ → Set)
                 (∼-equiv : ∀ d → IsEquivalence (λ σ σ' → σ ∼[ d ] σ'))
  where
  output-consistent : Set _
  output-consistent = ∀ {σ σ' a} → σ ∼[ dom a ] σ' → out σ a ≡ out σ' a

  step-consistent : Set _
  step-consistent = ∀ {σ σ' a d} → σ ∼[ d ] σ' → dom a ↝ d → do σ a ∼[ d ] do σ' a

  locally-respects : Set _
  locally-respects = ∀ {σ a d} → ¬ (dom a ↝ d) → σ ∼[ d ] do σ a

  module UnwindingCorrect (oc : output-consistent)
                          (sc : step-consistent)
                          (lc : locally-respects) where

    ∼-preorder : SD → Preorder _ _ _
    ∼-preorder d = record {
                     Carrier = Σ;
                     _≈_ = λ σ σ' → σ ∼[ d ] σ';
                     _∼_ = λ σ σ' → σ ∼[ d ] σ';
                     isPreorder = record { isEquivalence = ∼-equiv d
                                         ; reflexive = λ x → x
                                         ; trans = IsEquivalence.trans (∼-equiv d)} }

    lemma2 : ∀ {σ₁ σ₂ d} τ → σ₁ ∼[ d ] σ₂ → do⋆ σ₁ τ ∼[ d ] do⋆ σ₂ (purge τ d)
    lemma2 [] sim = sim
    lemma2 {d = d} (a ∷ τ) sim with dom a ↝? d
    lemma2 (a ∷ τ) sim | yes may-flow = sc (lemma2 τ sim) may-flow
    lemma2 {σ} {σ'} {d} (a ∷ τ) sim | no no-flow = begin
      do (do⋆ σ τ) a ≈⟨ sym (lc no-flow) ⟩
      do⋆ σ τ ≈⟨ lemma2 τ sim ⟩
      do⋆ σ' (purge τ d) ∎
      where open Pre (∼-preorder d)
            open Preorder (∼-preorder d)
            open IsEquivalence isEquivalence

    is-noninterferent : noninterferent
    is-noninterferent τ a = oc (lemma2 τ (IsEquivalence.refl (∼-equiv (dom a))))
