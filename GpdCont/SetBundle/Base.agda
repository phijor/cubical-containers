open import GpdCont.Prelude
module GpdCont.SetBundle.Base (ℓ : Level) where

open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryStrᴰ ; TwoCategoryᴰ)
open import GpdCont.TwoCategory.Displayed.LocallyThin as LT using (IsLocallyThinOver ; LocallyThinOver)
open import GpdCont.TwoCategory.HomotopyGroupoid
open import GpdCont.TwoCategory.Isomorphism using (module LocalIso)


open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (ΣPath≃PathΣ)

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

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

SetBundleᵀ : LocallyThinOver (hGpdCat ℓ) (ℓ-suc ℓ) ℓ ℓ
SetBundleᵀ .LocallyThinOver.ob[_] = S₀
SetBundleᵀ .LocallyThinOver.hom[_] = S₁
SetBundleᵀ .LocallyThinOver.rel[_] {yᴰ = Y} = S₂ {Y = Y}
SetBundleᵀ .LocallyThinOver.two-category-structureᴰ = SetBundleStrᴰ
SetBundleᵀ .LocallyThinOver.is-locally-thinᴰ = isLocallyThinBundleOver

SetBundleᴰ : TwoCategoryᴰ (hGpdCat ℓ) (ℓ-suc ℓ) ℓ ℓ
SetBundleᴰ = LocallyThinOver.toTwoCategoryᴰ SetBundleᵀ

SetBundle : TwoCategory (ℓ-suc ℓ) ℓ ℓ
SetBundle = LT.TotalTwoCategory.∫ (hGpdCat ℓ) SetBundleᵀ

private
  module SetBundleᴰ = TwoCategoryᴰ SetBundleᴰ
  module SetBundle = TwoCategory SetBundle

SetBundle₂≃Path : ∀ {x y} {f g : SetBundle.hom x y} → (SetBundle.rel {y = y} f g) ≃ (f ≡ g)
SetBundle₂≃Path = ΣPath≃PathΣ

module SetBundleNotation where
  open TwoCategory SetBundle public
  open TwoCategoryᴰ SetBundleᴰ public
  open LocallyThinOver SetBundleᵀ public using (relᴰPathP ; relᴰ≡ ; relΣPathP)

  Base : ob → hGroupoid ℓ
  Base = fst

  isGroupoidBase : (x : ob) → isGroupoid ⟨ Base x ⟩
  isGroupoidBase = str ∘ fst

  Fiber : (x : ob) (b : ⟨ Base x ⟩) → hSet ℓ
  Fiber (B , F) b = F b

  homBase[_,_] : (x y : ob) (f : hom x y) → ⟨ Base x ⟩ → ⟨ Base y ⟩
  homBase[_,_] x y = fst

  homBase : {x y : ob} (f : hom x y) → ⟨ Base x ⟩ → ⟨ Base y ⟩
  homBase {x} {y} = homBase[ x , y ]

  homFiber[_,_] : (x y : ob) (f : hom x y) → (b : ⟨ Base x ⟩) → ⟨ Fiber y (homBase[ x , y ] f b) ⟩ → ⟨ Fiber x b ⟩
  homFiber[_,_] x y = snd

  homFiber : {x y : ob} (f : hom x y) → (b : ⟨ Base x ⟩) → ⟨ Fiber y (homBase[ x , y ] f b) ⟩ → ⟨ Fiber x b ⟩
  homFiber {x} {y} = homFiber[ x , y ]

isLocallyGroupoidalSetBundle : LocalIso.isLocallyGroupoidal SetBundle
isLocallyGroupoidalSetBundle {x = G , X} {y = H , Y} {f = f , fᴰ} {g = g , gᴰ} (r , rᴰ) = goal where
  open import Cubical.Data.Sigma using (ΣPathP)

  r-inv : LocalIso.hasLocalInverse (hGpdCat _) r
  r-inv = isLocallyGroupoidalHGpdCat _ r

  module r-inv = LocalIso.isLocalInverse (r-inv .snd)

  r⁻ : hGpdCat.rel g f
  r⁻ = r-inv .fst

  rᴰ⁻ : S₂ {Y = Y} r⁻ gᴰ fᴰ
  rᴰ⁻ = symP rᴰ

  goal : LocalIso.hasLocalInverse SetBundle (r , rᴰ)
  goal .fst = r⁻ , rᴰ⁻
  goal .snd .LocalIso.isLocalInverse.dom-id i .fst = r-inv.dom-id i
  goal .snd .LocalIso.isLocalInverse.dom-id i .snd = rCancelP' (λ φ → S₁ φ X Y) r rᴰ i
  goal .snd .LocalIso.isLocalInverse.codom-id i .fst = r-inv.codom-id i
  goal .snd .LocalIso.isLocalInverse.codom-id i .snd = lCancelP' (λ φ → S₁ φ X Y) r rᴰ i

private module Sanity where
  sanity₀ : (SetBundle.ob) ≡ (Σ[ G ∈ hGroupoid ℓ ] (⟨ G ⟩ → hSet ℓ))
  sanity₀ = refl

  sanity₁ : ∀ {X Y} {Xᴰ Yᴰ} → (SetBundle.hom (X , Xᴰ) (Y , Yᴰ)) ≡ (Σ[ f ∈ (⟨ X ⟩ → ⟨ Y ⟩) ] ∀ g → ⟨ Yᴰ (f g) ⟩ → ⟨ Xᴰ g ⟩)
  sanity₁ = refl

  sanity₂ : ∀ {X Y : SetBundle.ob} {f g : SetBundle.hom X Y} →
    (SetBundle.rel {y = Y} f g) ≡ (Σ[ p ∈ f .fst ≡ g .fst ] PathP (λ i → (g : fst (X .fst)) → fst (Y .snd (p i g)) → fst (X .snd g)) (f .snd) (g .snd))
  sanity₂ = refl
