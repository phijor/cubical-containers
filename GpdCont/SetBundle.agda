module GpdCont.SetBundle where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryStrᴰ ; TwoCategoryᴰ)
open import GpdCont.TwoCategory.Displayed.LocallyThin as LT using (IsLocallyThinOver ; LocallyThinOver)
open import GpdCont.TwoCategory.HomotopyGroupoid


open import Cubical.Foundations.HLevels
import Cubical.Foundations.GroupoidLaws as GL
import Cubical.Foundations.Path as Path

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

module _ (ℓ : Level) where
  private
    module hGpdCat = TwoCategory (hGpdCat ℓ)
    variable
      G H K : hGpdCat.ob
      φ ψ ρ : hGpdCat.hom G H

    S₀ : hGpdCat.ob → Type _
    S₀ G = ⟨ G ⟩ → hSet ℓ

    S₁ : {G H : hGpdCat.ob} (φ : hGpdCat.hom G H) (X : S₀ G) (Y : S₀ H) → Type _
    S₁ φ X Y = ∀ g → ⟨ Y (φ g) ⟩ → ⟨ X g ⟩

    S₂ : ∀ {G H} {φ ψ : hGpdCat.hom G H}
      → {X : S₀ G} {Y : S₀ H}
      → (p : φ ≡ ψ)
      → (φᴰ : S₁ φ X Y) (ψᴰ : S₁ ψ X Y)
      → Type ℓ
    S₂ {X} {Y} p φᴰ ψᴰ = PathP (λ i → ∀ g → ⟨ Y (p i g) ⟩ → ⟨ X g ⟩) φᴰ ψᴰ

    {-# INJECTIVE_FOR_INFERENCE S₁ #-}
    {-# INJECTIVE_FOR_INFERENCE S₂ #-}

    isProp-S₂ : ∀ {G H} {φ ψ : hGpdCat.hom G H}
      → {X : S₀ G} {Y : S₀ H}
      → (p : φ ≡ ψ)
      → (φᴰ : S₁ φ X Y) (ψᴰ : S₁ ψ X Y)
      → isProp (S₂ {Y = Y} p φᴰ ψᴰ)
    isProp-S₂ {X} {Y} p = isOfHLevelPathP' {A = Motive} 1 isSetMotive where
      Motive : (i : I) → Type _
      Motive i = ∀ g → ⟨ Y (p i g) ⟩ → ⟨ X g ⟩

      isSetMotive : isSet (Motive i1)
      isSetMotive = isSetΠ λ g → isSet→ (str (X g))

    variable
      X : S₀ G
      Y : S₀ H

    S₁-id : ∀ {G} (X : S₀ G) → S₁ (hGpdCat.id-hom G) X X
    S₁-id X g = id ⟨ X g ⟩

    S₁-comp : ∀ {G H K : hGpdCat.ob} {φ : hGpdCat.hom G H} {ψ : hGpdCat.hom H K}
      → {X : S₀ G} {Y : S₀ H} {Z : S₀ K}
      → S₁ φ X Y → S₁ ψ Y Z → S₁ (φ hGpdCat.∙₁ ψ) X Z
    S₁-comp {φ} φᴰ ψᴰ = λ g → ψᴰ (φ g) ⋆ φᴰ g

    S₂-id : ∀ (φᴰ : S₁ φ X Y) → S₂ {Y = Y} (refl′ φ) φᴰ φᴰ
    S₂-id = refl′

    S₂-trans : ∀ {X : S₀ G} {Y : S₀ H} {φᴰ : S₁ φ X Y} {ψᴰ : S₁ ψ X Y} {ρᴰ : S₁ ρ X Y}
      → {p : φ ≡ ψ} {q : ψ ≡ ρ}
      → S₂ {Y = Y} p φᴰ ψᴰ
      → S₂ {Y = Y} q ψᴰ ρᴰ
      → S₂ {Y = Y} (p ∙ q) φᴰ ρᴰ
    S₂-trans {G} {H} {X} {Y} pᴰ qᴰ = compPathP' {A = hGpdCat.hom G H} {B = λ φ → S₁ φ X Y} pᴰ qᴰ

    -- Ahh yes, horizontal composition of dependent paths. What a beauty.
    -- This is defined in terms of horizontal composition of 1-cells:
    -- 2-cells (pᴰ : φ₁ᴰ ⇒ φ₂ᴰ), (qᴰ : ψ₁ᴰ ⇒ ψ₂ᴰ) are homotopies between 1-cells.
    -- Thus, at each point (i : I) along the homotopy, we can compose the 1-cells
    -- (pᴰ i : X → Y) and (qᴰ i : Y → Z).
    S₂-comp : ∀ {G H K : hGpdCat.ob}
      → {φ₁ φ₂ : hGpdCat.hom G H}
      → {ψ₁ ψ₂ : hGpdCat.hom H K}
      → {p : φ₁ ≡ φ₂}
      → {q : ψ₁ ≡ ψ₂}
      → {X : S₀ G} {Y : S₀ H} {Z : S₀ K}
      → {φ₁ᴰ : S₁ φ₁ X Y}
      → {φ₂ᴰ : S₁ φ₂ X Y}
      → {ψ₁ᴰ : S₁ ψ₁ Y Z}
      → {ψ₂ᴰ : S₁ ψ₂ Y Z}
      → (pᴰ : S₂ {Y = Y} p φ₁ᴰ φ₂ᴰ)
      → (qᴰ : S₂ {Y = Z} q ψ₁ᴰ ψ₂ᴰ)
      → S₂ {φ = φ₁ hGpdCat.∙₁ ψ₁} {ψ = φ₂ hGpdCat.∙₁ ψ₂} {Y = Z} (p hGpdCat.∙ₕ q)
        (S₁-comp {φ = φ₁} {ψ = ψ₁} {Z = Z} φ₁ᴰ ψ₁ᴰ)
        (S₁-comp {φ = φ₂} {ψ = ψ₂} {Z = Z} φ₂ᴰ ψ₂ᴰ)
    S₂-comp {p} {q} {Z} pᴰ qᴰ i = S₁-comp {φ = p i} {ψ = q i} {Z = Z} (pᴰ i) (qᴰ i)

    SetBundleStrᴰ : TwoCategoryStrᴰ (hGpdCat ℓ) (ℓ-suc ℓ) ℓ ℓ S₀ S₁ S₂
    SetBundleStrᴰ .TwoCategoryStrᴰ.id-homᴰ = S₁-id
    SetBundleStrᴰ .TwoCategoryStrᴰ.comp-homᴰ = S₁-comp
    SetBundleStrᴰ .TwoCategoryStrᴰ.id-relᴰ = S₂-id
    SetBundleStrᴰ .TwoCategoryStrᴰ.transᴰ = S₂-trans
    SetBundleStrᴰ .TwoCategoryStrᴰ.comp-relᴰ = S₂-comp

    isLocallyThinBundleOver : IsLocallyThinOver (hGpdCat ℓ) _ _ _ S₀ S₁ S₂ SetBundleStrᴰ
    isLocallyThinBundleOver .IsLocallyThinOver.is-prop-relᴰ {s} = isProp-S₂ s
    isLocallyThinBundleOver .IsLocallyThinOver.comp-hom-assocᴰ fᴰ gᴰ hᴰ = refl
    isLocallyThinBundleOver .IsLocallyThinOver.comp-hom-unit-leftᴰ gᴰ = refl
    isLocallyThinBundleOver .IsLocallyThinOver.comp-hom-unit-rightᴰ fᴰ = refl

  SetBundleᴰ : LocallyThinOver (hGpdCat ℓ) (ℓ-suc ℓ) ℓ ℓ
  SetBundleᴰ .LocallyThinOver.ob[_] = S₀
  SetBundleᴰ .LocallyThinOver.hom[_] = S₁
  SetBundleᴰ .LocallyThinOver.rel[_] {yᴰ = Y} = S₂ {Y = Y}
  SetBundleᴰ .LocallyThinOver.two-category-structureᴰ = SetBundleStrᴰ
  SetBundleᴰ .LocallyThinOver.is-locally-thinᴰ = isLocallyThinBundleOver

  SetBundle : TwoCategory (ℓ-suc ℓ) ℓ ℓ
  SetBundle = LT.TotalTwoCategory.∫ (hGpdCat ℓ) SetBundleᴰ

  private module Sanity where
    module SetBundle = TwoCategory SetBundle
    sanity₀ : (SetBundle.ob) ≡ (Σ[ G ∈ hGroupoid ℓ ] (⟨ G ⟩ → hSet ℓ))
    sanity₀ = refl

    sanity₁ : ∀ {X Y} {Xᴰ Yᴰ} → (SetBundle.hom (X , Xᴰ) (Y , Yᴰ)) ≡ (Σ[ f ∈ (⟨ X ⟩ → ⟨ Y ⟩) ] ∀ g → ⟨ Yᴰ (f g) ⟩ → ⟨ Xᴰ g ⟩)
    sanity₁ = refl

    sanity₂ : ∀ {X Y : SetBundle.ob} {f g : SetBundle.hom X Y} →
      (SetBundle.rel {y = Y} f g) ≡ (Σ[ p ∈ f .fst ≡ g .fst ] PathP (λ i → (g : fst (X .fst)) → fst (Y .snd (p i g)) → fst (X .snd g)) (f .snd) (g .snd))
    sanity₂ = refl

  module Pointed where
    open import GpdCont.TwoCategory.Subcategory
    open import Cubical.Foundations.Isomorphism using (section)
    open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
    Pointed₀ : hGpdCat.ob → Type _
    Pointed₀ (G , _) = ∥ G ∥₂ → G

    Pointed₁ : {G H : hGpdCat.ob} (f : hGpdCat.hom G H) (G⋆ : Pointed₀ G) (H⋆ : Pointed₀ H) → Type _
    Pointed₁ {G = (G , _)} {H = (H , _)} f G⋆ H⋆ = Path (∥ G ∥₂ → H) (G⋆ ⋆ f) (ST.map f ⋆ H⋆)

    Pointed₂ : {G H : hGpdCat.ob} {f g : hGpdCat.hom G H} {G⋆ : Pointed₀ G} {H⋆ : Pointed₀ H}
      → (f≡g : hGpdCat.rel f g)
      → (f⋆ : Pointed₁ f G⋆ H⋆)
      → (g⋆ : Pointed₁ g G⋆ H⋆)
      → Type _
    Pointed₂ {G = (G , _)} {H = (H , _)} {f} {g} {G⋆} {H⋆} f≡g f⋆ g⋆ = PathP (λ i → Path (∥ G ∥₂ → H) (G⋆ ⋆ f≡g i) (ST.map (f≡g i) ⋆ H⋆)) f⋆ g⋆

    isProp-Pointed₂ : {G H : hGpdCat.ob} {f g : hGpdCat.hom G H} {G⋆ : Pointed₀ G} {H⋆ : Pointed₀ H}
      → (f≡g : hGpdCat.rel f g)
      → (f⋆ : Pointed₁ f G⋆ H⋆)
      → (g⋆ : Pointed₁ g G⋆ H⋆)
      → isProp (Pointed₂ {H⋆ = H⋆} f≡g f⋆ g⋆)
    isProp-Pointed₂ {G} {H} f≡g = isOfHLevelPathP' 1 (isOfHLevelPath' 2 clue _ _) where
      clue : isGroupoid (∥ ⟨ G ⟩ ∥₂ → ⟨ H ⟩)
      clue = isGroupoidΠ λ _ → str H

    {-# INJECTIVE_FOR_INFERENCE Pointed₁ #-}
    {-# INJECTIVE_FOR_INFERENCE Pointed₂ #-}

    Pointed₁-id : ∀ {G} (G⋆ : Pointed₀ G) → Pointed₁ (id ⟨ G ⟩) G⋆ G⋆
    Pointed₁-id {G} G⋆ = funExt (ST.elim (λ x → str G (G⋆ x) (G⋆ (ST.map (id ⟨ G ⟩) x))) λ _ → refl)

    Pointed₁-comp : ∀ {G H K} {f : hGpdCat.hom G H} {g : hGpdCat.hom H K}
      → {G⋆ : Pointed₀ G} {H⋆ : Pointed₀ H} {K⋆ : Pointed₀ K}
      → (f⋆ : Pointed₁ f G⋆ H⋆)
      → (g⋆ : Pointed₁ g H⋆ K⋆)
      → Pointed₁ (f hGpdCat.∙₁ g) G⋆ K⋆
    Pointed₁-comp {K} {f} {g} {G⋆} {H⋆} {K⋆} f⋆ g⋆ = funExt (ST.elim (λ x → str K _ _) goal) where
      goal′ : ∀ x → (G⋆ ⋆ f ⋆ g) ST.∣ x ∣₂ ≡ K⋆ ST.∣ g (f x) ∣₂
      goal′ x = cong (λ · → g (· ST.∣ x ∣₂)) f⋆ ∙ (g⋆ ≡$S ST.∣ f x ∣₂)
      goal : ∀ x → (G⋆ ⋆ f ⋆ g) ST.∣ x ∣₂ ≡ (ST.map (f ⋆ g) ⋆ K⋆) ST.∣ x ∣₂
      goal = goal′

    Pointed₁-comp′ : ∀ {G H K} {f : hGpdCat.hom G H} {g : hGpdCat.hom H K}
      → {G⋆ : Pointed₀ G} {H⋆ : Pointed₀ H} {K⋆ : Pointed₀ K}
      → (f⋆ : Pointed₁ f G⋆ H⋆)
      → (g⋆ : Pointed₁ g H⋆ K⋆)
      → Pointed₁ (f hGpdCat.∙₁ g) G⋆ K⋆
    Pointed₁-comp′ {f} {g} {G⋆} {H⋆} {K⋆} f⋆ g⋆ = step₁ ∙∙ step₂ ∙∙ step₃ where
      step₁ : G⋆ ⋆ f ⋆ g ≡ ST.map f ⋆ H⋆ ⋆ g
      step₁ = cong (_⋆ g) f⋆

      step₂ : ST.map f ⋆ H⋆ ⋆ g ≡ ST.map f ⋆ ST.map g ⋆ K⋆
      step₂ = cong (ST.map f ⋆_) g⋆

      step₃ : ST.map f ⋆ ST.map g ⋆ K⋆ ≡ ST.map (f ⋆ g) ⋆ K⋆
      step₃ = cong (_⋆ K⋆) (ST.mapFunctorial f g)

    Pointed₂-id : ∀ {G H} {f : hGpdCat.hom G H} {G⋆ : Pointed₀ G} {H⋆ : Pointed₀ H} (f⋆ : Pointed₁ f G⋆ H⋆) → Pointed₂ {H⋆ = H⋆} (refl′ f) f⋆ f⋆
    Pointed₂-id f⋆ = refl′ f⋆

    Pointed₂-trans : ∀ {G H} {f g h : hGpdCat.hom G H} {G⋆ : Pointed₀ G} {H⋆ : Pointed₀ H} {p : f ≡ g} {q : g ≡ h}
      → {f⋆ : Pointed₁ f G⋆ H⋆}
      → {g⋆ : Pointed₁ g G⋆ H⋆}
      → {h⋆ : Pointed₁ h G⋆ H⋆}
      → Pointed₂ {H⋆ = H⋆} p f⋆ g⋆
      → Pointed₂ {H⋆ = H⋆} q g⋆ h⋆
      → Pointed₂ {H⋆ = H⋆} (p ∙ q) f⋆ h⋆
    Pointed₂-trans {G} {H} {G⋆} {H⋆} pᴰ qᴰ = compPathP' {A = hGpdCat.hom G H} {B = λ f → Pointed₁ f G⋆ H⋆} pᴰ qᴰ

    Pointed₂-comp : ∀ {G H K} {f₁ f₂ : hGpdCat.hom G H} {g₁ g₂ : hGpdCat.hom H K}
      → {p : f₁ ≡ f₂} {q : g₁ ≡ g₂}
      → {G⋆ : Pointed₀ G} {H⋆ : Pointed₀ H} {K⋆ : Pointed₀ K}
      → {f₁⋆ : Pointed₁ f₁ G⋆ H⋆}
      → {f₂⋆ : Pointed₁ f₂ G⋆ H⋆}
      → {g₁⋆ : Pointed₁ g₁ H⋆ K⋆}
      → {g₂⋆ : Pointed₁ g₂ H⋆ K⋆}
      → (pᴰ : Pointed₂ {H⋆ = H⋆} p f₁⋆ f₂⋆)
      → (qᴰ : Pointed₂ {H⋆ = K⋆} q g₁⋆ g₂⋆)
      → Pointed₂ {H⋆ = K⋆} (p hGpdCat.∙ₕ q) (Pointed₁-comp f₁⋆ g₁⋆) (Pointed₁-comp f₂⋆ g₂⋆)
    Pointed₂-comp pᴰ qᴰ i = Pointed₁-comp (pᴰ i) (qᴰ i)

    PointedStrᴰ : TwoCategoryStrᴰ (hGpdCat ℓ) ℓ ℓ ℓ Pointed₀ Pointed₁ Pointed₂
    PointedStrᴰ .TwoCategoryStrᴰ.id-homᴰ = Pointed₁-id
    PointedStrᴰ .TwoCategoryStrᴰ.comp-homᴰ = Pointed₁-comp
    PointedStrᴰ .TwoCategoryStrᴰ.id-relᴰ = Pointed₂-id
    PointedStrᴰ .TwoCategoryStrᴰ.transᴰ = Pointed₂-trans
    PointedStrᴰ .TwoCategoryStrᴰ.comp-relᴰ = Pointed₂-comp

    isLocallyThinOverPointedStr : IsLocallyThinOver (hGpdCat ℓ) ℓ ℓ ℓ _ _ _ PointedStrᴰ
    isLocallyThinOverPointedStr .IsLocallyThinOver.is-prop-relᴰ {s} = isProp-Pointed₂ s
    isLocallyThinOverPointedStr .IsLocallyThinOver.comp-hom-assocᴰ f⋆ g⋆ h⋆ = funExtSquare _ _ _ _ (ST.elim {! !} λ x → the (_ ≡ _) {! !}) where
    isLocallyThinOverPointedStr .IsLocallyThinOver.comp-hom-unit-leftᴰ = {! !}
    isLocallyThinOverPointedStr .IsLocallyThinOver.comp-hom-unit-rightᴰ = {! !}

    Pointedᴰ : LocallyThinOver (hGpdCat ℓ) ℓ ℓ ℓ
    Pointedᴰ .LocallyThinOver.ob[_] = Pointed₀
    Pointedᴰ .LocallyThinOver.hom[_] = Pointed₁
    Pointedᴰ .LocallyThinOver.rel[_] {yᴰ = H⋆} = Pointed₂ {H⋆ = H⋆}
    Pointedᴰ .LocallyThinOver.two-category-structureᴰ = PointedStrᴰ
    Pointedᴰ .LocallyThinOver.is-locally-thinᴰ = isLocallyThinOverPointedStr

    Pointed : TwoCategory (ℓ-suc ℓ) ℓ ℓ
    Pointed = LT.TotalTwoCategory.∫ (hGpdCat ℓ) Pointedᴰ

    hasSectionPointed : Pointed .TwoCategory.ob → hProp ℓ
    hasSectionPointed (G , G⋆) .fst = section ST.∣_∣₂ G⋆
    hasSectionPointed (G , G⋆) .snd = isPropΠ λ (x : ∥ ⟨ G ⟩ ∥₂) → ST.isSetSetTrunc (ST.∣ G⋆ x ∣₂) x

    WellPointed : TwoCategory _ _ _
    WellPointed = Subcategory Pointed hasSectionPointed
