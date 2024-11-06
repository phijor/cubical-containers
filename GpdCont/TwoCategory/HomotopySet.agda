module GpdCont.TwoCategory.HomotopySet where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LocallyThin

open import Cubical.Foundations.HLevels as HLevels using (hSet)
open import Cubical.Foundations.Isomorphism using (invIso)
import      Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Categories.Instances.Sets using (SET)
import      Cubical.Data.Equality as Eq

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

module _ (ℓ : Level) where
  hSetCat : TwoCategory (ℓ-suc ℓ) ℓ ℓ
  hSetCat = FromCategory.LocallyThin (SET ℓ)

  -- Alternate definition of the thin 2-category of sets
  -- with the inductive indentity type for 2-cells.
  -- This is useful to avoid transport-hell when defining
  -- structure displayed over these 2-cells, as one can
  -- use path induction to define new types.
  private
    SetEq₀ : Type (ℓ-suc ℓ)
    SetEq₀ = hSet ℓ

    SetEq₁ : (x y : SetEq₀) → Type ℓ
    SetEq₁ x y = ⟨ x ⟩ → ⟨ y ⟩
    {-# INJECTIVE_FOR_INFERENCE SetEq₁ #-}

    SetEq₂ : {x y : SetEq₀} → (f g : SetEq₁ x y) → Type ℓ
    SetEq₂ f g = f Eq.≡ g
    {-# INJECTIVE_FOR_INFERENCE SetEq₂ #-}

    isPropSetEq₂ : ∀ {x y} (f g : SetEq₁ x y) → isProp (SetEq₂ f g)
    isPropSetEq₂ {y} f g = HLevels.isOfHLevelRetractFromIso 1 path-iso is-prop-path where
      path-iso : Iso (f Eq.≡ g) (Path _ f g)
      path-iso = invIso Eq.PathIsoEq

      is-prop-path : isProp (Path _ f g)
      is-prop-path = HLevels.isSet→ (str y) f g

  SetStr : TwoCategoryStr SetEq₀ SetEq₁ SetEq₂
  SetStr .TwoCategoryStr.id-hom x = id ⟨ x ⟩
  SetStr .TwoCategoryStr.comp-hom = _⋆_
  SetStr .TwoCategoryStr.id-rel f = Eq.refl
  SetStr .TwoCategoryStr.trans r s = r Eq.∙ s
  SetStr .TwoCategoryStr.comp-rel Eq.refl Eq.refl = Eq.refl

  opaque
    isTwoCategorySetStr : IsTwoCategory _ _ _ SetStr
    isTwoCategorySetStr .IsTwoCategory.is-set-rel f g = isProp→isSet $ isPropSetEq₂ f g
    isTwoCategorySetStr .IsTwoCategory.trans-assoc r s t = Eq.eqToPath (Eq.assoc r s t)
    isTwoCategorySetStr .IsTwoCategory.trans-unit-left s = Eq.eqToPath Eq.refl
    isTwoCategorySetStr .IsTwoCategory.trans-unit-right s = Eq.eqToPath (Eq.unitR s)
    isTwoCategorySetStr .IsTwoCategory.comp-rel-id f g = refl
    isTwoCategorySetStr .IsTwoCategory.comp-rel-trans Eq.refl Eq.refl Eq.refl Eq.refl = refl
    isTwoCategorySetStr .IsTwoCategory.comp-hom-assoc f g h = refl
    isTwoCategorySetStr .IsTwoCategory.comp-hom-unit-left g = refl
    isTwoCategorySetStr .IsTwoCategory.comp-hom-unit-right f = refl
    isTwoCategorySetStr .IsTwoCategory.comp-rel-assoc Eq.refl Eq.refl Eq.refl = refl
    isTwoCategorySetStr .IsTwoCategory.comp-rel-unit-left Eq.refl = refl
    isTwoCategorySetStr .IsTwoCategory.comp-rel-unit-right Eq.refl = refl

  SetEq : TwoCategory (ℓ-suc ℓ) ℓ ℓ
  SetEq .TwoCategory.ob = SetEq₀
  SetEq .TwoCategory.hom = SetEq₁
  SetEq .TwoCategory.rel = SetEq₂
  SetEq .TwoCategory.two-category-structure = SetStr
  SetEq .TwoCategory.is-two-category = isTwoCategorySetStr

  private
    module SetEq = TwoCategory SetEq

  isLocallyThinSetEq : isLocallyThin SetEq
  isLocallyThinSetEq = isPropSetEq₂
