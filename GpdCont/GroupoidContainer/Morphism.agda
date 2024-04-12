module GpdCont.GroupoidContainer.Morphism where

open import GpdCont.Prelude
open import GpdCont.GroupoidContainer.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level
    G H K L : GCont ℓ

record GContMorphism {ℓ} (G H : GCont ℓ) : Type (ℓ-suc ℓ) where
  private
    module G = GCont G
    module H = GCont H

  field
    shape-mor : G.Shape → H.Shape
    pos-path : ∀ (s : G.Shape) → H.Pos (shape-mor s) → G.Pos s

open GCont
open GContMorphism

GContMorphism≡ : {α β : GContMorphism G H}
  → (p : α .shape-mor ≡ β .shape-mor)
  → (q : ∀ s → PathP (λ i → H .Pos (p i s) → G .Pos s) (α .pos-path s) (β .pos-path s))
  → α ≡ β
GContMorphism≡ p q i .GContMorphism.shape-mor s = p i s
GContMorphism≡ p q i .GContMorphism.pos-path s = q s i

GContId : (G : GCont ℓ) → GContMorphism G G
GContId G .GContMorphism.shape-mor = id $ G .Shape
GContId G .GContMorphism.pos-path s = id $ G .Pos s

compGContMorphism : (α : GContMorphism G H) (β : GContMorphism H K) → GContMorphism G K
compGContMorphism {G} {H} {K} α β = composite where
  module α = GContMorphism α
  module β = GContMorphism β

  composite : GContMorphism G K
  composite .shape-mor = β.shape-mor ∘ α.shape-mor
  composite .pos-path s = α.pos-path s ∘ β.pos-path (α .shape-mor s)

infixl 15 _⋆GCont_
_⋆GCont_ : (α : GContMorphism G H) (β : GContMorphism H K) → GContMorphism G K
_⋆GCont_ = compGContMorphism

compGContMorphismIdL : (α : GContMorphism G H) → GContId G ⋆GCont α ≡ α
compGContMorphismIdL α = refl

compGContMorphismIdR : (α : GContMorphism G H) → α ⋆GCont GContId H ≡ α
compGContMorphismIdR α = refl

compGContMorphismAssoc : (α : GContMorphism G H) (β : GContMorphism H K) (γ : GContMorphism K L) → (α ⋆GCont β) ⋆GCont γ ≡ α ⋆GCont (β ⋆GCont γ)
compGContMorphismAssoc α β γ = refl
