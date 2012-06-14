open import Data.List

module StateMachines where

record DetStateMachine : Set₁ where
  field
    Σ A O : Set
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

