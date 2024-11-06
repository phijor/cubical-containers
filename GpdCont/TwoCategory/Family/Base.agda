module GpdCont.TwoCategory.Family.Base where

open import GpdCont.Prelude
open import GpdCont.HomotopySet
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.HomotopySet using (SetEq ; isTwoCategorySetStr)
open import GpdCont.TwoCategory.Displayed.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
import      Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Functions.FunExtEquiv
import      Cubical.Data.Equality as Eq

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

module _ {ℓo ℓh ℓr} (C : TwoCategory ℓo ℓh ℓr) (ℓ : Level) where

  private
    module C = TwoCategory C
    module SetEq = TwoCategory (SetEq ℓ)

    Fam₀ : SetEq.ob → Type (ℓ-max ℓo ℓ)
    Fam₀ x = ⟨ x ⟩ → C.ob
    {-# INJECTIVE_FOR_INFERENCE Fam₀ #-}

    Fam₁ : {x y : SetEq.ob}
      → (f : SetEq.hom x y)
      → (xᴰ : Fam₀ x) (yᴰ : Fam₀ y) → Type (ℓ-max ℓh ℓ)
    Fam₁ {x} f xᴰ yᴰ = (j : ⟨ x ⟩) → C.hom (xᴰ j) (yᴰ (f j))
    {-# INJECTIVE_FOR_INFERENCE Fam₁ #-}

    Fam₂[_] : {x y : SetEq.ob} {f g : SetEq.hom x y}
      → {xᴰ : Fam₀ x}
      → (yᴰ : Fam₀ y)
      → (r : SetEq.rel f g)
      → (fᴰ : Fam₁ f xᴰ yᴰ)
      → (gᴰ : Fam₁ g xᴰ yᴰ)
      → Type (ℓ-max ℓr ℓ)
    Fam₂[_] {x} yᴰ Eq.refl fᴰ gᴰ = (j : ⟨ x ⟩) → C.rel (fᴰ j) (gᴰ j)

    Fam₂ : {x y : SetEq.ob} {f g : SetEq.hom x y}
      → {xᴰ : Fam₀ x}
      → {yᴰ : Fam₀ y}
      → (r : SetEq.rel f g)
      → (fᴰ : Fam₁ f xᴰ yᴰ)
      → (gᴰ : Fam₁ g xᴰ yᴰ)
      → Type (ℓ-max ℓr ℓ)
    Fam₂ {yᴰ} = Fam₂[ yᴰ ]
    {-# INJECTIVE_FOR_INFERENCE Fam₂[_] #-}
    {-# INJECTIVE_FOR_INFERENCE Fam₂ #-}


    Fam₁-comp[_] : ∀ {x y z : SetEq.ob} {f : SetEq.hom x y} {g : SetEq.hom y z}
      → {xᴰ : Fam₀ x} {yᴰ : Fam₀ y} (zᴰ : Fam₀ z)
      → (fᴰ : Fam₁ f xᴰ yᴰ)
      → (gᴰ : Fam₁ g yᴰ zᴰ)
      → Fam₁ (SetEq.comp-hom f g) xᴰ zᴰ
    Fam₁-comp[_] {f} zᴰ fᴰ gᴰ j = fᴰ j C.∙₁ gᴰ (f j)

    Fam₁-comp : ∀ {x y z : SetEq.ob} {f : SetEq.hom x y} {g : SetEq.hom y z}
      → {xᴰ : Fam₀ x} {yᴰ : Fam₀ y} {zᴰ : Fam₀ z}
      → (fᴰ : Fam₁ f xᴰ yᴰ)
      → (gᴰ : Fam₁ g yᴰ zᴰ)
      → Fam₁ (SetEq.comp-hom f g) xᴰ zᴰ
    Fam₁-comp {zᴰ} = Fam₁-comp[ zᴰ ]

    _∙ᵥ_ : ∀ {x y : SetEq.ob} {f g h : SetEq.hom x y} {r : SetEq.rel f g} {s : SetEq.rel g h}
      → {xᴰ : Fam₀ x} {yᴰ : Fam₀ y}
      → {fᴰ : Fam₁ f xᴰ yᴰ}
      → {gᴰ : Fam₁ g xᴰ yᴰ}
      → {hᴰ : Fam₁ h xᴰ yᴰ}
      → (rᴰ : Fam₂[ yᴰ ] r fᴰ gᴰ)
      → (sᴰ : Fam₂[ yᴰ ] s gᴰ hᴰ)
      → (Fam₂[ yᴰ ] (SetEq.trans r s) fᴰ hᴰ)
    _∙ᵥ_ {r = Eq.refl} {s = Eq.refl} rᴰ sᴰ j = C.trans (rᴰ j) (sᴰ j)

    _∙ₕ_ : ∀ {x y z : SetEq.ob} {f₁ f₂ : SetEq.hom x y} {g₁ g₂ : SetEq.hom y z}
      → {r : SetEq.rel f₁ f₂} {s : SetEq.rel g₁ g₂}
      → {xᴰ : Fam₀ x} {yᴰ : Fam₀ y} {zᴰ : Fam₀ z}
      → {f₁ᴰ : Fam₁ f₁ xᴰ yᴰ}
      → {f₂ᴰ : Fam₁ f₂ xᴰ yᴰ}
      → {g₁ᴰ : Fam₁ g₁ yᴰ zᴰ}
      → {g₂ᴰ : Fam₁ g₂ yᴰ zᴰ}
      → (rᴰ : Fam₂[ yᴰ ] r f₁ᴰ f₂ᴰ)
      → (sᴰ : Fam₂[ zᴰ ] s g₁ᴰ g₂ᴰ)
      → Fam₂[ zᴰ ] (SetEq.comp-rel r s) (Fam₁-comp[ zᴰ ] f₁ᴰ g₁ᴰ) (Fam₁-comp[ zᴰ ] f₂ᴰ g₂ᴰ)
    _∙ₕ_ {f₁} {r = Eq.refl} {s = Eq.refl} rᴰ sᴰ j = C.comp-rel (rᴰ j) (sᴰ (f₁ j))

    opaque
      isSetFam₂ : ∀ {x y} {f g : SetEq.hom x y} (s : SetEq.rel f g)
        → {xᴰ : Fam₀ x} {yᴰ : Fam₀ y}
        → (fᴰ : Fam₁ f xᴰ yᴰ)
        → (gᴰ : Fam₁ g xᴰ yᴰ)
        → isSet (Fam₂[ yᴰ ] s fᴰ gᴰ)
      isSetFam₂ Eq.refl  fᴰ gᴰ = isSetΠ λ j → C.is-set-rel (fᴰ j) (gᴰ j)

  FamStrᴰ : TwoCategoryStrᴰ (SetEq ℓ) _ _ _ Fam₀ Fam₁ Fam₂
  FamStrᴰ .TwoCategoryStrᴰ.id-homᴰ xᴰ j = C.id-hom (xᴰ j)
  FamStrᴰ .TwoCategoryStrᴰ.comp-homᴰ {zᴰ} fᴰ gᴰ = Fam₁-comp[ zᴰ ] fᴰ gᴰ
  FamStrᴰ .TwoCategoryStrᴰ.id-relᴰ {yᴰ} fᴰ j = C.id-rel (fᴰ j)
  FamStrᴰ .TwoCategoryStrᴰ.transᴰ {yᴰ} rᴰ sᴰ = _∙ᵥ_ {yᴰ = yᴰ} rᴰ sᴰ
  FamStrᴰ .TwoCategoryStrᴰ.comp-relᴰ = _∙ₕ_

  opaque
    unfolding isTwoCategorySetStr
    isTwoCategoryFamᴰ : IsTwoCategoryᴰ (SetEq ℓ) _ _ _ Fam₀ Fam₁ Fam₂ FamStrᴰ
    isTwoCategoryFamᴰ .IsTwoCategoryᴰ.is-set-relᴰ {s} = isSetFam₂ s
    isTwoCategoryFamᴰ .IsTwoCategoryᴰ.trans-assocᴰ {r = Eq.refl} {s = Eq.refl} {t = Eq.refl} rᴰ sᴰ tᴰ = funExt λ j → C.trans-assoc (rᴰ j) (sᴰ j) (tᴰ j)
    isTwoCategoryFamᴰ .IsTwoCategoryᴰ.trans-unit-leftᴰ {s = Eq.refl} sᴰ = funExt λ j → C.trans-unit-left (sᴰ j)
    isTwoCategoryFamᴰ .IsTwoCategoryᴰ.trans-unit-rightᴰ {r = Eq.refl} rᴰ = funExt λ j → C.trans-unit-right (rᴰ j)
    isTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-rel-idᴰ {f} fᴰ gᴰ = funExt λ j → C.comp-rel-id (fᴰ j) (gᴰ (f j))
    isTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-rel-transᴰ {f₁} {s = Eq.refl} {t = Eq.refl} {u = Eq.refl} {v = Eq.refl} sᴰ tᴰ uᴰ vᴰ = funExt λ j → C.comp-rel-trans (sᴰ j) (tᴰ j) (uᴰ (f₁ j)) (vᴰ (f₁ j))
    isTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-hom-assocᴰ {f} {g} fᴰ gᴰ hᴰ = funExt λ j → C.comp-hom-assoc (fᴰ j) (gᴰ (f j)) (hᴰ (g (f j)))
    isTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-hom-unit-leftᴰ gᴰ = funExt λ j → C.comp-hom-unit-left (gᴰ j)
    isTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-hom-unit-rightᴰ fᴰ = funExt λ j → C.comp-hom-unit-right (fᴰ j)
    isTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-rel-assocᴰ {f₁} {g₁} {s = Eq.refl} {t = Eq.refl} {u = Eq.refl} sᴰ tᴰ uᴰ = funExt λ j → C.comp-rel-assoc (sᴰ j) (tᴰ (f₁ j)) (uᴰ (g₁ (f₁ j)))
    isTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-rel-unit-leftᴰ {s = Eq.refl} sᴰ = funExt λ j → C.comp-rel-unit-left (sᴰ j)
    isTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-rel-unit-rightᴰ {r = Eq.refl} rᴰ = funExt λ j → C.comp-rel-unit-right (rᴰ j)


  Famᴰ : TwoCategoryᴰ (SetEq ℓ) (ℓ-max ℓo ℓ) (ℓ-max ℓh ℓ) (ℓ-max ℓr ℓ)
  Famᴰ .TwoCategoryᴰ.ob[_] = Fam₀
  Famᴰ .TwoCategoryᴰ.hom[_] = Fam₁
  Famᴰ .TwoCategoryᴰ.rel[_] {yᴰ} = Fam₂[ yᴰ ]
  Famᴰ .TwoCategoryᴰ.two-category-structureᴰ = FamStrᴰ
  Famᴰ .TwoCategoryᴰ.is-two-categoryᴰ = isTwoCategoryFamᴰ

  Fam : TwoCategory (ℓ-max ℓo (ℓ-suc ℓ)) (ℓ-max ℓh ℓ) (ℓ-max ℓr ℓ)
  Fam = TotalTwoCategory.∫ (SetEq ℓ) Famᴰ
