open import Data.List
open import Data.Product renaming (Σ to Σt)
open import Data.Sum
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Algebra
open import Level

module ComputationalModels where

record DetStateMachine {ℓ₁ ℓ₂ ℓ₃} : Set (Level.suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Σ : Set ℓ₁
    A : Set ℓ₂
    O : Set ℓ₃
    σ₀ : Σ
    do : Σ → A → Σ
    out : Σ → A → O

  do⋆ : Σ → List A → Σ
  do⋆ σ [] = σ
  do⋆ σ (a ∷ as) = do (do⋆ σ as) a

  run : List A → Σ
  run = do⋆ σ₀

  output : List A → A → O
  output as a = out (run as) a

record NondetStateMachine {ℓ} : Set (Level.suc ℓ) where
  field
    Σ A O : Set ℓ
    σ₀ : Σ
    do : Σ → A → Σ → Set ℓ
    do-non-empty : ∀ σ a → ∃ (λ σ' → do σ a σ')
    out : Σ → A → O → Set ℓ
    out-non-empty : ∀ σ a → ∃ (λ o → out σ a o)

  do⋆ : (Σ → Set ℓ) → List A → Σ → Set ℓ
  do⋆ σs [] σ' = σs σ'
  do⋆ σs (a ∷ as) σ' = ∃ (λ σ'' → do⋆ σs as σ'' × do σ'' a σ')

  run : List A → Σ → Set ℓ
  run = do⋆ (_≡_ σ₀)

  output : List A → A → O → Set ℓ
  output as a o = ∃ (λ σ → run as σ × out σ a o)

record EventSystem {ℓ} : Set (Level.suc ℓ) where
  field
    E : Set ℓ
    I : E → Set ℓ
    O : E → Set ℓ
    I-O-disjoint : ∀ e → (I e → ¬ O e) × (O e → ¬ I e)
    Tr : List E → Set ℓ
    prefix-closed : ∀ {x} xs → Tr (xs ∷ʳ x) → Tr xs


↓_↓ : ∀ {A : Set} → (List A → Set) → (List A → Set)
↓ P ↓ xs = ∃ λ ys → P (xs ++ ys)

↓-correct : ∀ {A : Set} (P : List A → Set) → ∀ {x} xs → ↓ P ↓ (xs ∷ʳ x) → ↓ P ↓ xs
↓-correct P {x} [] (proj₁ , proj₂) = x ∷ proj₁ , proj₂
↓-correct P {x} (x₁ ∷ xs) p = ↓-correct (λ z → P (x₁ ∷ z)) xs p

↓-sup : ∀ {A : Set} (P : List A → Set) {xs} → P xs → ↓ P ↓ xs
↓-sup P {xs} p = [] , subst P (sym (proj₂ (Monoid.identity (monoid _)) xs)) p

_↾_ : {ℓ : Level} {A : Set ℓ} {P : A → Set ℓ} → List A → (∀ xs → Dec (P xs)) → List A
[] ↾ p = []
(x ∷ xs) ↾ p with p x
(x ∷ xs) ↾ p | yes p₁ = x ∷ xs ↾ p
(x ∷ xs) ↾ p | no ¬p = xs ↾ p

record StateEventSystem {ℓ₁ ℓ₂} : Set (Level.suc (ℓ₁ ⊔ ℓ₂)) where
  field
    S : Set ℓ₁
    E : Set ℓ₂
    I , O : E → Set ℓ₂
    I-O-disjoint : ∀ e → (I e → ¬ O e) × (O e → ¬ I e)
    T : S → E → S → Set (ℓ₁ ⊔ ℓ₂)
    deterministic : ∀ {s s' s'' e} → T s e s' → T s e s'' → s' ≡ s''