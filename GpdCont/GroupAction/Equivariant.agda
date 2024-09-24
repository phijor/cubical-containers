module GpdCont.GroupAction.Equivariant where

open import GpdCont.Prelude
open import GpdCont.GroupAction.Base

open import Cubical.Algebra.Group.Base
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level
    G H : Group ℓ
    X Y : hSet ℓ
    σ : Action G X
    τ : Action H Y

open Action

isEquivariantMap : (σ : Action G X) (τ : Action H Y) (f : ⟨ X ⟩ → ⟨ Y ⟩) → Type _
isEquivariantMap σ τ f = ∀ g → (f ∘ σ .action g .fst) ≡ ({! !} ∘ f)

EquivariantMap : (σ : Action G X) (τ : Action H Y) → Type _
EquivariantMap {X} {Y} σ τ = Σ (⟨ X ⟩ → ⟨ Y ⟩) (isEquivariantMap σ τ)
