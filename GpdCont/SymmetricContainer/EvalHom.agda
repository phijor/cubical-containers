open import GpdCont.SymmetricContainer.Base

module GpdCont.SymmetricContainer.EvalHom where

open import GpdCont.Prelude
open import GpdCont.SymmetricContainer.Morphism

import GpdCont.SymmetricContainer.Eval as Eval

open import Cubical.Foundations.HLevels
private
  variable
    ℓ : Level
    G H : SymmetricContainer ℓ

open Eval using (⟦_⟧ᵗ ; ⟦_⟧ ; ⟦_⟧-map ; ⟦-⟧ᵗ-Path ; shape ; label)

open Morphism

Hom⟦_⟧ᵗ : (α : Morphism G H) → (X : Type ℓ) → ⟦ G ⟧ᵗ X → ⟦ H ⟧ᵗ X
Hom⟦ α ⟧ᵗ X p .shape = α .shape-map (p .shape)
Hom⟦ α ⟧ᵗ X p .label = p .label ∘ (α .pos-map (p .shape))

Hom⟦_⟧₀ : (α : Morphism G H) → (X : hGroupoid ℓ) → ⟨ ⟦ G ⟧ X ⟩ → ⟨ ⟦ H ⟧ X ⟩
Hom⟦ α ⟧₀ (X , is-gpd-X) = Hom⟦ α ⟧ᵗ X

Hom⟦_⟧₀-natural : (α : Morphism G H) → (X Y : hGroupoid ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) → (Hom⟦ α ⟧₀ Y ∘ ⟦ G ⟧-map X Y f) ≡ (⟦ H ⟧-map X Y f ∘ Hom⟦ α ⟧₀ X)
Hom⟦_⟧₀-natural α X Y f = refl

Hom⟦_⟧₀-id : ∀ (X : hGroupoid ℓ) x → Hom⟦ idMorphism G ⟧₀ X x ≡ x
Hom⟦_⟧₀-id {G = G} X q = refl
