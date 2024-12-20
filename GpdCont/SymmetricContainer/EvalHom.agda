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

open GContMorphism

Hom⟦_⟧ᵗ : (α : GContMorphism G H) → (X : Type ℓ) → ⟦ G ⟧ᵗ X → ⟦ H ⟧ᵗ X
Hom⟦ α ⟧ᵗ X p .shape = α .shape-mor (p .shape)
Hom⟦ α ⟧ᵗ X p .label = p .label ∘ (α .pos-path (p .shape))

Hom⟦_⟧₀ : (α : GContMorphism G H) → (X : hGroupoid ℓ) → ⟨ ⟦ G ⟧ X ⟩ → ⟨ ⟦ H ⟧ X ⟩
Hom⟦ α ⟧₀ (X , is-gpd-X) = Hom⟦ α ⟧ᵗ X

Hom⟦_⟧₀-natural : (α : GContMorphism G H) → (X Y : hGroupoid ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) → (Hom⟦ α ⟧₀ Y ∘ ⟦ G ⟧-map X Y f) ≡ (⟦ H ⟧-map X Y f ∘ Hom⟦ α ⟧₀ X)
Hom⟦_⟧₀-natural α X Y f = refl

Hom⟦_⟧₀-id : ∀ (X : hGroupoid ℓ) x → Hom⟦ GContId G ⟧₀ X x ≡ x
Hom⟦_⟧₀-id {G = G} X q = refl

private
  Π-nat-equiv : {A : Type} {B C : A → Type} → Iso ((∀ a → B a) → (∀ a → C a)) (∀ a → B a → C a)
  Π-nat-equiv .Iso.fun f = λ a b → f (λ a′ → {! !}) a
  Π-nat-equiv .Iso.inv g = λ Πb a → g a (Πb a)
  Π-nat-equiv .Iso.rightInv = {! !}
  Π-nat-equiv .Iso.leftInv = {! !}
