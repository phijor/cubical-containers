module GpdCont.GroupoidContainer.Morphism where

open import GpdCont.Prelude
open import GpdCont.GroupoidContainer.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ : Level
    G H K L : GCont ℓ

record GContMorphism {ℓ} (G H : GCont ℓ) : Type ℓ where
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

private
  _≡Mor_ : (α β : GContMorphism G H) → Type _
  _≡Mor_ {G} {H} α β = Σ[ p ∈ α .shape-mor ≡ β .shape-mor ] (∀ s → PathP (λ i → H .Pos (p i s) → G .Pos s) (α .pos-path s) (β .pos-path s))

module _ {α β : GContMorphism G H} where
  GContMorphism≡Iso : Iso (α ≡Mor β) (α ≡ β)
  GContMorphism≡Iso .Iso.fun = uncurry GContMorphism≡
  GContMorphism≡Iso .Iso.inv p .fst i = p i .shape-mor
  GContMorphism≡Iso .Iso.inv p .snd s i = p i .pos-path s
  GContMorphism≡Iso .Iso.rightInv p i j .shape-mor = p j .shape-mor
  GContMorphism≡Iso .Iso.rightInv p i j .pos-path = p j .pos-path
  GContMorphism≡Iso .Iso.leftInv p i .fst j = p .fst j
  GContMorphism≡Iso .Iso.leftInv p i .snd s = p .snd s

  GContMorphism≡Equiv : (α ≡Mor β) ≃ (α ≡ β)
  GContMorphism≡Equiv = isoToEquiv GContMorphism≡Iso

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

private
  open import Cubical.Data.Unit
  open import Cubical.Data.Bool
  open import Cubical.Data.Sum
  open import Cubical.Data.Sigma
  open import Cubical.Functions.Involution

  data UPairShape : Type where
    ⋆ : UPairShape
    swap : ⋆ ≡ ⋆
    mul : compSquareFiller swap swap refl
    trunc𝔹2 : isGroupoid UPairShape

  upair-rec : ∀ {ℓ} {B : Type ℓ}
    → (isGroupoid B)
    → (b : B)
    → (p : b ≡ b)
    → (p² : p ∙ p ≡ refl)
    → UPairShape → B
  upair-rec {B} is-gpd-B b p p² = go where
    go : _ → _
    go ⋆ = b
    go (swap i) = p i
    go (mul i j) = goal i j where
      goal : compSquareFiller p p refl
      goal = coerceCompSquareFiller p²
    go (trunc𝔹2 x y p q r s i j k) = is-gpd-B (go x) (go y) (cong go p) (cong go q) (cong (cong go) r) (cong (cong go) s) i j k

  UPairPos : UPairShape → hSet _
  UPairPos = upair-rec isGroupoidHSet (Bool , isSetBool) (TypeOfHLevel≡ 2 notEq) (ΣSquareSet (λ X → isProp→isSet isPropIsSet) (involPathComp notnot))

  UPair : GCont ℓ-zero
  UPair .Shape = UPairShape
  UPair .Pos = ⟨_⟩ ∘ UPairPos
  UPair .is-groupoid-shape = trunc𝔹2
  UPair .is-set-pos = str ∘ UPairPos

  _⊗_ : GCont ℓ → GCont ℓ → GCont ℓ
  G ⊗ H = record
    { Shape = G .Shape × H .Shape
    ; Pos = λ { (g , h) → G .Pos g ⊎ H .Pos h }
    ; is-groupoid-shape = isGroupoid× (G .is-groupoid-shape) (H .is-groupoid-shape)
    ; is-set-pos = λ { (g , h) → isSet⊎ (G .is-set-pos g) (H .is-set-pos h) }
    }

  Id : GCont ℓ-zero
  Id .Shape = Unit
  Id .Pos _ = Unit
  Id .is-groupoid-shape = isOfHLevelUnit 3
  Id .is-set-pos _ = isOfHLevelUnit 2

  proj-right : GContMorphism (G ⊗ H) H
  proj-right .shape-mor = snd
  proj-right .pos-path _ = inr

  π₁ : GContMorphism (Id ⊗ UPair) UPair
  π₁ = proj-right {G = Id} {H = UPair}
