open import Data.Bool
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

bools-disjoint : ∀ {ℓ} {A : Set ℓ} → (b b' : A → Bool) → Set ℓ
bools-disjoint b b' = ∀ a → (T (b a) → ¬ T (b' a)) × (T (b' a) → ¬ T (b a))

record EventSystem {ℓ} : Set (Level.suc ℓ) where
  field
    E : Set ℓ
    I : E → Bool
    O : E → Bool
    I-O-disjoint : bools-disjoint I O
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
    I : E → Bool
    O : E → Bool
    I-O-disjoint : bools-disjoint I O
    Ts : S → E → S → Set (ℓ₁ ⊔ ℓ₂)
    deterministic : ∀ {s s' s'' e} → Ts s e s' → Ts s e s'' → s' ≡ s''

SES : ∀ {ℓ} → EventSystem {ℓ} → StateEventSystem {ℓ} {ℓ}
SES ES = record {
           E = E;
           S = List E;
           I = I;
           O = O;
           I-O-disjoint = I-O-disjoint;
           Ts = Ts;
           deterministic = λ {s} ts ts' → det {s} ts ts' }
  where open EventSystem ES
        Ts : List E → E → List E → Set _
        Ts s e s' = Tr (s ∷ʳ e) × s' ≡ s ∷ʳ e
        det : ∀ {s s' s'' e} → Ts s e s' → Ts s e s'' → s' ≡ s''
        det (_ , eq₁) (_ , eq₂) rewrite eq₁ | eq₂ = refl
