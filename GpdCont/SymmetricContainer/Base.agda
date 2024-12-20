module GpdCont.SymmetricContainer.Base where

open import GpdCont.Prelude
open import Cubical.Foundations.HLevels

record SymmetricContainer (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Shape : Type ℓ
    Pos : Shape → Type ℓ

  field
    is-groupoid-shape : isGroupoid Shape
    is-set-pos : ∀ s → isSet (Pos s)

  opaque
    ShapeGroupoid : hGroupoid ℓ
    ShapeGroupoid .fst = Shape
    ShapeGroupoid .snd = is-groupoid-shape

    PosSet : (s : Shape) → hSet ℓ
    PosSet s .fst = Pos s
    PosSet s .snd = is-set-pos s

mkSymmetricContainer : ∀ {ℓ} → (S : hGroupoid ℓ) (P : ⟨ S ⟩ → hSet ℓ) → SymmetricContainer ℓ
mkSymmetricContainer S P .SymmetricContainer.Shape = ⟨ S ⟩
mkSymmetricContainer S P .SymmetricContainer.Pos = ⟨_⟩ ∘ P
mkSymmetricContainer S P .SymmetricContainer.is-groupoid-shape = str S
mkSymmetricContainer S P .SymmetricContainer.is-set-pos = str ∘ P

syntax mkSymmetricContainer S (λ s → P) = [ s ∈ S ◁ P ]

private module _ where
  open import Cubical.HITs.Susp as Susp using (Susp)
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
  open import Cubical.Data.Bool
  open import Cubical.Data.Sum as Sum using (_⊎_)

  𝟜 = Bool ⊎ Bool

  S = Susp Bool
  P : S → Type
  P Susp.north = 𝟜
  P Susp.south = 𝟜
  P (Susp.merid false i) = notEq i ⊎ Bool
  P (Susp.merid true i) = Bool ⊎ notEq i

  isSet-P : ∀ s → isSet (P s)
  isSet-P Susp.north = Sum.isSet⊎ isSetBool isSetBool
  isSet-P Susp.south = Sum.isSet⊎ isSetBool isSetBool
  isSet-P (Susp.merid a i) = isProp→PathP {B = λ i → isSet (P (Susp.merid a i))} (λ i → isPropIsSet) (isSet-P Susp.north) (isSet-P Susp.south) i

  ΩS = ∥ S ∥₂

  -- Not true : s = t = north, p = refl , q = east ∙ west:
  -- cong P p = refl
  -- cong P q = cong P east ∙ cong P west = notEq ⊕ notEq
  lemma : (s t : S) → (p q : s ≡ t) → cong P p ≡ cong P q
  lemma = Susp.suspToPropElim2 true {! !} {! !}

  ΩP : ΩS → hSet ℓ-zero
  ΩP = ST.rec→Gpd.fun (isOfHLevelTypeOfHLevel 2) (λ s → P s , isSet-P s) λ { s t p q i j → lemma s t p q i j , {! !} }

  ΩP′ : ΩS → Type
  ΩP′ ST.∣ x ∣₂ = 𝟜
  ΩP′ (ST.squash₂ ST.∣ x ∣₂ ST.∣ x₁ ∣₂ p q i j) = {! !}
  ΩP′ (ST.squash₂ ST.∣ x ∣₂ (ST.squash₂ t t₁ p₁ q₁ i₁ i₂) p q i j) = {! !}
  ΩP′ (ST.squash₂ (ST.squash₂ s s₁ p₁ q₁ i₁ i₂) t p q i j) = {! !}
