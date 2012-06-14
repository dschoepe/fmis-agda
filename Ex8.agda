open import StateMachines
open import Policies

open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PropEq

module Ex8 where
  module Ex8-3
    (M : DetStateMachine)
    (SC : DecSecurityPolicy)
    (dom : DetStateMachine.A M → DecSecurityPolicy.SD SC) where

    open DetStateMachine M
    open DecSecurityPolicy SC
    import Noninterference as NI
    open NI SC M dom

    data Right : Set where
      view : Right
      modify : Right

    module AC (Obj V : Set) (val : Obj → Σ → V) (R : SD → Obj → Right → Set) where
      open PropEq

      _≈[_]_ : Σ → SD → Σ → Set
      σ₁ ≈[ d ] σ₂ = ∀ o → R d o view → val o σ₁ ≡ val o σ₂

      ≈-sym : ∀ {d} → Symmetric (λ σ σ' → σ ≈[ d ] σ')
      ≈-sym p o viewable = sym (p o viewable)

      ≈-trans : ∀ {d} → Transitive (λ σ σ' → σ ≈[ d ] σ')
      ≈-trans a≈b b≈c o viewable rewrite a≈b o viewable | b≈c o viewable = refl

      ≈-equiv : ∀ d → IsEquivalence (λ σ σ' → σ ≈[ d ] σ')
      ≈-equiv d = record { refl = λ _ _ → refl
                         ; sym = ≈-sym
                         ; trans = ≈-trans
                         }

      module AC-correct
        (propA1 : ∀ {d₁ d₂ o} → R d₁ o modify → R d₂ o view → d₁ ↝ d₂)
        (propA2 : ∀ {d₁ d₂ o} → d₁ ↝ d₂ → R d₁ o view → R d₂ o view)
        (propB1 : ∀ {σ o a} → val o σ ≢ val o (do σ a) → R (dom a) o modify)
        (propB2 : ∀ {σ₁ σ₂ a} → σ₁ ≈[ dom a ] σ₂ → out σ₁ a ≡ out σ₂ a)
        (propB3 : ∀ {σ σ' o a} →
              val o σ ≢ val o (do σ a) →
              σ ≈[ dom a ] σ' →
              val o (do σ a) ≡ val o (do σ' a))
        (_≟_ : Decidable (_≡_ {A = V}))
        (R-dec : ∀ {d o r} → Dec (R d o r))
        where

        open Unwinding _≈[_]_ ≈-equiv
        contrapos2 : ∀ {P Q R : Set} → (P → Q → R) → Dec P → ¬ R → ¬ P ⊎ ¬ Q
        contrapos2 f (yes p) ¬R = inj₂ (λ x → ¬R (f p x))
        contrapos2 f (no ¬p) ¬R = inj₁ ¬p

        ¬¬-dec-elim : ∀ {P : Set} → Dec P → ¬ (¬ P) → P
        ¬¬-dec-elim (yes p) np = p
        ¬¬-dec-elim (no ¬p) np = ⊥-elim (np ¬p)


        output-cons : output-consistent
        output-cons = propB2

        step-cons : step-consistent
        step-cons {σ} {σ'} {a} σ≈[d]σ' doma↝d o viewable
          with (val o σ ≟ val o (do σ a))
        step-cons {σ} {σ'} {a} σ≈[d]σ' doma↝d o viewable | yes eq with (val o σ' ≟ val o (do σ' a))
        step-cons σ≈[d]σ' doma↝d o viewable | yes eq | yes eq' rewrite sym eq | sym eq' =
          σ≈[d]σ' o viewable
        step-cons {σ} {σ'} {a} σ≈[d]σ' doma↝d o viewable | yes eq | no ¬eq' =
          sym (propB3 ¬eq' (λ o₁ viewable₁ → ≈-sym σ≈[d]σ' o₁ (propA2 doma↝d viewable₁)))
        step-cons σ≈[d]σ' doma↝d o viewable | no ¬eq =
          propB3 ¬eq (λ o₁ z → σ≈[d]σ' o₁ (propA2 doma↝d z))

        locally-resp : locally-respects
        locally-resp noFlow o viewable
          with contrapos2 propA1 R-dec noFlow
        ... | inj₁ noMod = ¬¬-dec-elim (_ ≟ _) (contraposition propB1 noMod)
        ... | inj₂ noView = ⊥-elim (noView viewable)

        noninterf : noninterferent
        noninterf = UnwindingCorrect.is-noninterferent output-cons step-cons locally-resp
