module GpdCont.SymmetricContainer.Morphism where

open import GpdCont.Prelude
open import GpdCont.SymmetricContainer.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ : Level
    G H K L : SymmetricContainer ℓ

record Morphism {ℓ} (G H : SymmetricContainer ℓ) : Type ℓ where
  private
    module G = SymmetricContainer G
    module H = SymmetricContainer H

  field
    shape-map : G.Shape → H.Shape
    pos-map : ∀ (s : G.Shape) → H.Pos (shape-map s) → G.Pos s

open SymmetricContainer
open Morphism

unquoteDecl MorphismIsoΣ = declareRecordIsoΣ MorphismIsoΣ (quote Morphism)

instance
  MorphismToΣ : ∀ {G H : SymmetricContainer ℓ} → RecordToΣ (Morphism G H)
  MorphismToΣ {G} {H} = toΣ (MorphismIsoΣ {G = G} {H = H})

Morphism≡ : {α β : Morphism G H}
  → (p : α .shape-map ≡ β .shape-map)
  → (q : ∀ s → PathP (λ i → H .Pos (p i s) → G .Pos s) (α .pos-map s) (β .pos-map s))
  → α ≡ β
Morphism≡ p q i .Morphism.shape-map s = p i s
Morphism≡ p q i .Morphism.pos-map s = q s i

MorphismSquare : {α β γ δ : Morphism G H}
  → {p : α ≡ β}
  → {q : β ≡ δ}
  → {r : γ ≡ δ}
  → {s : α ≡ γ}
  → (shape-square : Square (cong shape-map p) (cong shape-map r) (cong shape-map s) (cong shape-map q))
  → Square p r s q
MorphismSquare {G} {H} {α} {β} {γ} {δ} {p} {q} {r} {s} sq = mor-square where
  module G = SymmetricContainer G
  module H = SymmetricContainer H

  isSetPosMap : (u : G.Shape → H.Shape) → isSet (∀ s → H.Pos (u s) → G.Pos s)
  isSetPosMap u = isSetΠ λ s → isSet→ (G.is-set-pos s)

  -- Mhhhh, casting soup!
  mor-square : Square p r s q
  mor-square i j = cast←Σ $ ΣSquareSet isSetPosMap {p = cong cast→Σ p} {q = cong cast→Σ q} {r = cong cast→Σ r} {s = cong cast→Σ s} sq i j


private
  _≡Mor_ : (α β : Morphism G H) → Type _
  _≡Mor_ {G} {H} α β = Σ[ p ∈ α .shape-map ≡ β .shape-map ] (∀ s → PathP (λ i → H .Pos (p i s) → G .Pos s) (α .pos-map s) (β .pos-map s))

module _ {α β : Morphism G H} where
  Morphism≡Iso : Iso (α ≡Mor β) (α ≡ β)
  Morphism≡Iso .Iso.fun = uncurry Morphism≡
  Morphism≡Iso .Iso.inv p .fst i = p i .shape-map
  Morphism≡Iso .Iso.inv p .snd s i = p i .pos-map s
  Morphism≡Iso .Iso.sec p i j .shape-map = p j .shape-map
  Morphism≡Iso .Iso.sec p i j .pos-map = p j .pos-map
  Morphism≡Iso .Iso.ret p i .fst j = p .fst j
  Morphism≡Iso .Iso.ret p i .snd s = p .snd s

  Morphism≡Equiv : (α ≡Mor β) ≃ (α ≡ β)
  Morphism≡Equiv = isoToEquiv Morphism≡Iso

isGroupoidMorphism : isGroupoid (Morphism G H)
isGroupoidMorphism {G} {H} = recordIsOfHLevel 3 $
  isGroupoidΣ
    (isGroupoidΠ λ _ → H .is-groupoid-shape)
    λ u → isSet→isGroupoid (isSetΠ2 λ s _ → G .is-set-pos s)

idMorphism : (G : SymmetricContainer ℓ) → Morphism G G
idMorphism G .Morphism.shape-map = id $ G .Shape
idMorphism G .Morphism.pos-map s = id $ G .Pos s

compMorphism : (α : Morphism G H) (β : Morphism H K) → Morphism G K
compMorphism {G} {H} {K} α β = composite where
  module α = Morphism α
  module β = Morphism β

  composite : Morphism G K
  composite .shape-map = β.shape-map ∘ α.shape-map
  composite .pos-map s = α.pos-map s ∘ β.pos-map (α .shape-map s)

infixl 15 _⋆Mor_
_⋆Mor_ : (α : Morphism G H) (β : Morphism H K) → Morphism G K
_⋆Mor_ = compMorphism

compMorphismIdL : (α : Morphism G H) → idMorphism G ⋆Mor α ≡ α
compMorphismIdL α = refl

compMorphismIdR : (α : Morphism G H) → α ⋆Mor idMorphism H ≡ α
compMorphismIdR α = refl

compMorphismAssoc : (α : Morphism G H) (β : Morphism H K) (γ : Morphism K L) → (α ⋆Mor β) ⋆Mor γ ≡ α ⋆Mor (β ⋆Mor γ)
compMorphismAssoc α β γ = refl

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

  UPair : SymmetricContainer ℓ-zero
  UPair .Shape = UPairShape
  UPair .Pos = ⟨_⟩ ∘ UPairPos
  UPair .is-groupoid-shape = trunc𝔹2
  UPair .is-set-pos = str ∘ UPairPos

  _⊗_ : SymmetricContainer ℓ → SymmetricContainer ℓ → SymmetricContainer ℓ
  G ⊗ H = record
    { Shape = G .Shape × H .Shape
    ; Pos = λ { (g , h) → G .Pos g ⊎ H .Pos h }
    ; is-groupoid-shape = isGroupoid× (G .is-groupoid-shape) (H .is-groupoid-shape)
    ; is-set-pos = λ { (g , h) → isSet⊎ (G .is-set-pos g) (H .is-set-pos h) }
    }

  Id : SymmetricContainer ℓ-zero
  Id .Shape = Unit
  Id .Pos _ = Unit
  Id .is-groupoid-shape = isOfHLevelUnit 3
  Id .is-set-pos _ = isOfHLevelUnit 2

  proj-right : Morphism (G ⊗ H) H
  proj-right .shape-map = snd
  proj-right .pos-map _ = inr

  π₁ : Morphism (Id ⊗ UPair) UPair
  π₁ = proj-right {G = Id} {H = UPair}
