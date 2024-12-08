open import GpdCont.Prelude
module GpdCont.SetBundle.Pointed (ℓ : Level) where

open import GpdCont.SetBundle.Base ℓ
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryStrᴰ ; TwoCategoryᴰ)
open import GpdCont.TwoCategory.Displayed.LocallyThin as LT using (IsLocallyThinOver ; LocallyThinOver)
open import GpdCont.TwoCategory.HomotopyGroupoid using (hGpdCat)

open import Cubical.Foundations.HLevels
open import GpdCont.TwoCategory.Subcategory
open import Cubical.Foundations.Isomorphism using (section)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

private
  module hGpdCat = TwoCategory (hGpdCat ℓ)

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
isLocallyThinOverPointedStr .IsLocallyThinOver.comp-hom-assocᴰ f⋆ g⋆ h⋆ = funExtSquare _ _ _ _ (ST.elim {! !} λ x → the (_ ≡ _) {! !})
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
