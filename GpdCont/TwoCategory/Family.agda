module GpdCont.TwoCategory.Family where

open import GpdCont.Prelude
open import GpdCont.HomotopySet
open import GpdCont.TwoCategory.Base
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

    SetEq₀ : Type (ℓ-suc ℓ)
    SetEq₀ = hSet ℓ

    SetEq₁ : (x y : SetEq₀) → Type ℓ
    SetEq₁ x y = ⟨ x ⟩ → ⟨ y ⟩
    {-# INJECTIVE_FOR_INFERENCE SetEq₁ #-}

    SetEq₂ : {x y : SetEq₀} → (f g : SetEq₁ x y) → Type ℓ
    SetEq₂ f g = f Eq.≡ g
    {-# INJECTIVE_FOR_INFERENCE SetEq₂ #-}

    SetStr : TwoCategoryStr SetEq₀ SetEq₁ SetEq₂
    SetStr .TwoCategoryStr.id-hom x = id ⟨ x ⟩
    SetStr .TwoCategoryStr.comp-hom = _⋆_
    SetStr .TwoCategoryStr.id-rel f = Eq.refl
    SetStr .TwoCategoryStr.trans r s = r Eq.∙ s
    SetStr .TwoCategoryStr.comp-rel Eq.refl Eq.refl = Eq.refl

    opaque
      isTwoCategorySetStr : IsTwoCategory _ _ _ SetStr
      isTwoCategorySetStr .IsTwoCategory.is-set-rel {y} f g = is-set-eq where
        is-set-eq : isSet (f Eq.≡ g)
        is-set-eq = isOfHLevelRetractFromIso 2 (invIso $ Eq.PathIsoEq) $ isGroupoidΠ (const $ isSet→isGroupoid (str y)) f g
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

  FamStrᴰ : TwoCategoryStrᴰ SetEq _ _ _ Fam₀ Fam₁ Fam₂
  FamStrᴰ .TwoCategoryStrᴰ.id-homᴰ xᴰ j = C.id-hom (xᴰ j)
  FamStrᴰ .TwoCategoryStrᴰ.comp-homᴰ {zᴰ} fᴰ gᴰ = Fam₁-comp[ zᴰ ] fᴰ gᴰ
  FamStrᴰ .TwoCategoryStrᴰ.id-relᴰ {yᴰ} fᴰ j = C.id-rel (fᴰ j)
  FamStrᴰ .TwoCategoryStrᴰ.transᴰ {yᴰ} rᴰ sᴰ = _∙ᵥ_ {yᴰ = yᴰ} rᴰ sᴰ
  FamStrᴰ .TwoCategoryStrᴰ.comp-relᴰ = _∙ₕ_

  opaque
    unfolding isTwoCategorySetStr
    IsTwoCategoryFamᴰ : IsTwoCategoryᴰ SetEq _ _ _ Fam₀ Fam₁ Fam₂ FamStrᴰ
    IsTwoCategoryFamᴰ .IsTwoCategoryᴰ.is-set-relᴰ {s} = isSetFam₂ s
    IsTwoCategoryFamᴰ .IsTwoCategoryᴰ.trans-assocᴰ {r = Eq.refl} {s = Eq.refl} {t = Eq.refl} rᴰ sᴰ tᴰ = funExt λ j → C.trans-assoc (rᴰ j) (sᴰ j) (tᴰ j)
    IsTwoCategoryFamᴰ .IsTwoCategoryᴰ.trans-unit-leftᴰ {s = Eq.refl} sᴰ = funExt λ j → C.trans-unit-left (sᴰ j)
    IsTwoCategoryFamᴰ .IsTwoCategoryᴰ.trans-unit-rightᴰ {r = Eq.refl} rᴰ = funExt λ j → C.trans-unit-right (rᴰ j)
    IsTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-rel-idᴰ {f} fᴰ gᴰ = funExt λ j → C.comp-rel-id (fᴰ j) (gᴰ (f j))
    IsTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-rel-transᴰ {f₁} {s = Eq.refl} {t = Eq.refl} {u = Eq.refl} {v = Eq.refl} sᴰ tᴰ uᴰ vᴰ = funExt λ j → C.comp-rel-trans (sᴰ j) (tᴰ j) (uᴰ (f₁ j)) (vᴰ (f₁ j))
    IsTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-hom-assocᴰ {f} {g} fᴰ gᴰ hᴰ = funExt λ j → C.comp-hom-assoc (fᴰ j) (gᴰ (f j)) (hᴰ (g (f j)))
    IsTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-hom-unit-leftᴰ gᴰ = funExt λ j → C.comp-hom-unit-left (gᴰ j)
    IsTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-hom-unit-rightᴰ fᴰ = funExt λ j → C.comp-hom-unit-right (fᴰ j)
    IsTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-rel-assocᴰ {f₁} {g₁} {s = Eq.refl} {t = Eq.refl} {u = Eq.refl} sᴰ tᴰ uᴰ = funExt λ j → C.comp-rel-assoc (sᴰ j) (tᴰ (f₁ j)) (uᴰ (g₁ (f₁ j)))
    IsTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-rel-unit-leftᴰ {s = Eq.refl} sᴰ = funExt λ j → C.comp-rel-unit-left (sᴰ j)
    IsTwoCategoryFamᴰ .IsTwoCategoryᴰ.comp-rel-unit-rightᴰ {r = Eq.refl} rᴰ = funExt λ j → C.comp-rel-unit-right (rᴰ j)


  Famᴰ : TwoCategoryᴰ SetEq (ℓ-max ℓo ℓ) (ℓ-max ℓh ℓ) (ℓ-max ℓr ℓ)
  Famᴰ .TwoCategoryᴰ.ob[_] = Fam₀
  Famᴰ .TwoCategoryᴰ.hom[_] = Fam₁
  Famᴰ .TwoCategoryᴰ.rel[_] {yᴰ} = Fam₂[ yᴰ ]
  Famᴰ .TwoCategoryᴰ.two-category-structureᴰ = FamStrᴰ
  Famᴰ .TwoCategoryᴰ.is-two-categoryᴰ = IsTwoCategoryFamᴰ

  Fam : TwoCategory (ℓ-max ℓo (ℓ-suc ℓ)) (ℓ-max ℓh ℓ) (ℓ-max ℓr ℓ)
  Fam = TotalTwoCategory.∫ SetEq Famᴰ
