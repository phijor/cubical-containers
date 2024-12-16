module GpdCont.GroupAction.Integer where

open import GpdCont.Prelude
open import GpdCont.GroupAction.Base

open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base using (Group)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom)
open import Cubical.HITs.FreeGroup as FG using (freeGroupGroup)

ℤ : Group ℓ-zero
ℤ = freeGroupGroup Unit

1ℤ : ⟨ ℤ ⟩
1ℤ = FG.η tt

ℤ-rec : ∀ {ℓ} {G : Group ℓ} (g₀ : ⟨ G ⟩) → GroupHom ℤ G
ℤ-rec g₀ = FG.rec (λ _ → g₀)

ℤ-action : ∀ {ℓ} {X : hSet ℓ} (σ : ⟨ X ⟩ ≃ ⟨ X ⟩) → Action ℤ X
ℤ-action = GroupHom→Action ∘ ℤ-rec
