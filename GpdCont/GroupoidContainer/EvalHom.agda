open import GpdCont.GroupoidContainer.Base

module GpdCont.GroupoidContainer.EvalHom {ℓ} {G H : GCont ℓ} where

open import GpdCont.Prelude
open import GpdCont.GroupoidContainer.Morphism

import GpdCont.GroupoidContainer.Eval as Eval

module G = Eval G
module H = Eval H

open GContMorphism

opaque
  unfolding Eval.⟦_⟧ᵗ
  Hom⟦_⟧₀ : (α : GContMorphism G H) → (∀ X → G.⟦ X ⟧ᵗ) → (∀ X → H.⟦ X ⟧ᵗ)
  Hom⟦ α ⟧₀ F X .fst = α .shape-mor (F X .fst)
  Hom⟦ α ⟧₀ F X .snd = F X .snd ∘ transport (α .pos-path (F X .fst))
