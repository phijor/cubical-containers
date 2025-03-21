open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.StrictFunctor

module GpdCont.TwoCategory.Algebra {ℓo ℓh ℓr} {C : TwoCategory ℓo ℓh ℓr} (F : StrictFunctor C C) where

open import GpdCont.TwoCategory.Displayed.Base
open import GpdCont.TwoCategory.Isomorphism using (module LocalIso)
open import GpdCont.TwoCategory.Initial

private
  module C where
    open TwoCategory C public
    open LocalIso C using () renaming (LocalIso to rel-iso ; idLocalIso to rel-id-iso) public


  module F = StrictFunctor F

Algebraᴰ₀ : (x : C.ob) → Type _
Algebraᴰ₀ x = C.hom (F.₀ x) x

Algebraᴰ₁ : ∀ {x y} (f : C.hom x y) → Algebraᴰ₀ x → Algebraᴰ₀ y → Type _
Algebraᴰ₁ f xᴰ yᴰ = C.rel-iso (xᴰ C.∙₁ f) (F.₁ f C.∙₁ yᴰ)

Algebraᴰ₂ : ∀ {x y} {f g : C.hom x y} (r : C.rel f g)
  → {xᴰ : Algebraᴰ₀ x} {yᴰ : Algebraᴰ₀ y}
  → (fᴰ : Algebraᴰ₁ f xᴰ yᴰ)
  → (gᴰ : Algebraᴰ₁ g xᴰ yᴰ)
  → Type _
Algebraᴰ₂ {f} {g} r {xᴰ} {yᴰ} (fᴰ , _) (gᴰ , _) = rhs ≡ lhs where
  lhs : C.rel (xᴰ C.∙₁ f) (F.₁ g C.∙₁ yᴰ)
  lhs = (xᴰ C.◁ r) C.∙ᵥ gᴰ

  rhs : C.rel (xᴰ C.∙₁ f) (F.₁ g C.∙₁ yᴰ)
  rhs = fᴰ C.∙ᵥ (F.₂ r C.▷ yᴰ)

alg-id-hom : ∀ {x} (xᴰ : Algebraᴰ₀ x) → Algebraᴰ₁ (C.id-hom x) xᴰ xᴰ
alg-id-hom {x} xᴰ = goal where
  goal' : C.rel-iso xᴰ xᴰ
  goal' = C.rel-id-iso xᴰ

  -- iso₁ : C.rel-iso (xᴰ C.∙₁ C.id-hom x) xᴰ
  -- iso₁ .fst = C.pathToRel (C.comp-hom-unit-right xᴰ)
  -- iso₁ .snd .fst = C.pathToRel (sym (C.comp-hom-unit-right xᴰ))
  -- iso₁ .snd .snd .LocalIso.isLocalInverse.dom-id = {! !}
  -- iso₁ .snd .snd .LocalIso.isLocalInverse.codom-id = {! !}

  -- iso₂ : C.rel-iso xᴰ (C.id-hom (F.₀ x) C.∙₁ xᴰ)
  -- iso₂ .fst = {! !}
  -- iso₂ .snd = {! !}

  goal : C.rel-iso (xᴰ C.∙₁ C.id-hom x) (F.₁ (C.id-hom x) C.∙₁ xᴰ)
  goal = subst2 C.rel-iso (sym (C.comp-hom-unit-right xᴰ)) (sym (C.comp-hom-unit-left xᴰ) ∙ cong (C._∙₁ xᴰ) (F.F-hom-id x)) goal'

Algebraᴰ : TwoCategoryᴰ C ℓh ℓr ℓr
Algebraᴰ .TwoCategoryᴰ.ob[_] = Algebraᴰ₀
Algebraᴰ .TwoCategoryᴰ.hom[_] = Algebraᴰ₁
Algebraᴰ .TwoCategoryᴰ.rel[_] r fᴰ gᴰ = Algebraᴰ₂ r fᴰ gᴰ
Algebraᴰ .TwoCategoryᴰ.two-category-structureᴰ .TwoCategoryStrᴰ.id-homᴰ = alg-id-hom
Algebraᴰ .TwoCategoryᴰ.two-category-structureᴰ .TwoCategoryStrᴰ.comp-homᴰ = {! !}
Algebraᴰ .TwoCategoryᴰ.two-category-structureᴰ .TwoCategoryStrᴰ.id-relᴰ = {! !}
Algebraᴰ .TwoCategoryᴰ.two-category-structureᴰ .TwoCategoryStrᴰ.transᴰ = {! !}
Algebraᴰ .TwoCategoryᴰ.two-category-structureᴰ .TwoCategoryStrᴰ.comp-relᴰ = {! !}
Algebraᴰ .TwoCategoryᴰ.is-two-categoryᴰ = {! !}

Algebra : TwoCategory (ℓ-max ℓo ℓh) (ℓ-max ℓh ℓr) ℓr
Algebra = TotalTwoCategory.∫ C Algebraᴰ

InitialAlgebra : Type _
InitialAlgebra = Initial Algebra

module Algebra where
  open TwoCategory Algebra public

  ₁≡ : ∀ {x y : ob} {f g : hom x y} (p : f .fst ≡ g .fst) → PathP (λ i → Algebraᴰ₁ (p i) (x .snd) (y .snd)) (f .snd) (g .snd) → f ≡ g
  ₁≡ = TotalTwoCategory.∫₁≡ C Algebraᴰ
