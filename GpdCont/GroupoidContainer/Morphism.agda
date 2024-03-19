module GpdCont.GroupoidContainer.Morphism where

open import GpdCont.Prelude
open import GpdCont.GroupoidContainer.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level
    G H : GCont ℓ

record GContMorphism {ℓ} (G H : GCont ℓ) : Type (ℓ-suc ℓ) where
  private
    module G = GCont G
    module H = GCont H

  field
    shape-mor : G.Shape → H.Shape
    pos-path : ∀ (s : G.Shape) → H.Pos (shape-mor s) ≡ G.Pos s

open GContMorphism

GContMorphism≡ : {α β : GContMorphism G H}
  → (p : α .shape-mor ≡ β .shape-mor)
  → (q : ∀ s → ?)
  → α ≡ β
GContMorphism≡ p q i .GContMorphism.shape-mor s = p i s
GContMorphism≡ p q i .GContMorphism.pos-path s j = {! !}

GContId : (G : GCont ℓ) → GContMorphism G G
GContId G .GContMorphism.shape-mor = id $ G .GCont.Shape
GContId G .GContMorphism.pos-path s = refl
