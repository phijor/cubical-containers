module GpdCont.TwoCategory.Displayed.LocallyThin where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Displayed.Base as Disp hiding (module TotalTwoCategory)

open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (Σ≡Prop)

module _ {ℓo ℓh ℓr} (C : TwoCategory ℓo ℓh ℓr) (ℓoᴰ ℓhᴰ ℓrᴰ : Level) where
  private
    ℓC = ℓ-of C
    ℓCᴰ : Level
    ℓCᴰ = ℓMax ℓoᴰ ℓhᴰ ℓrᴰ
    module C = TwoCategory C

  module _
    (ob[_] : C.ob → Type ℓoᴰ)
    (hom[_] : {x y : C.ob} (f : C.hom x y) (xᴰ : ob[ x ]) (yᴰ : ob[ y ]) → Type ℓhᴰ)
    (rel[_] : {x y : C.ob} {f g : C.hom x y}
      → {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
      → (s : C.rel f g)
      → (fᴰ : hom[ f ] xᴰ yᴰ)
      → (gᴰ : hom[ g ] xᴰ yᴰ)
      → Type ℓrᴰ)
    where
      open C

      record IsLocallyThinOver (sᴰ : TwoCategoryStrᴰ C ℓoᴰ ℓhᴰ ℓrᴰ ob[_] hom[_] rel[_]) : Type (ℓ-max ℓC ℓCᴰ) where
        private
          open module sᴰ = TwoCategoryStrᴰ sᴰ

        field
          is-prop-relᴰ : {x y : ob} {f g : hom x y} {s : rel f g}
            → {xᴰ : ob[ x ]}
            → {yᴰ : ob[ y ]}
            → (fᴰ : hom[ f ] xᴰ yᴰ)
            → (gᴰ : hom[ g ] xᴰ yᴰ)
            → isProp (rel[ s ] fᴰ gᴰ)

        field
          comp-hom-assocᴰ : {x y z w : C.ob} {f : C.hom x y} {g : C.hom y z} {h : C.hom z w}
            → {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]} {wᴰ : ob[ w ]}
            → (fᴰ : hom[ f ] xᴰ yᴰ)
            → (gᴰ : hom[ g ] yᴰ zᴰ)
            → (hᴰ : hom[ h ] zᴰ wᴰ)
            → PathP (λ i → hom[ C.comp-hom-assoc f g h i ] xᴰ wᴰ)
                ((fᴰ ∙₁ᴰ gᴰ) ∙₁ᴰ hᴰ)
                (fᴰ ∙₁ᴰ (gᴰ ∙₁ᴰ hᴰ))
          
          comp-hom-unit-leftᴰ : {x y : C.ob} {g : C.hom x y}
            → {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
            → (gᴰ : hom[ g ] xᴰ yᴰ)
            → PathP (λ i → hom[ C.comp-hom-unit-left g i ] xᴰ yᴰ)
                (id-homᴰ xᴰ ∙₁ᴰ gᴰ)
                gᴰ

          comp-hom-unit-rightᴰ : {x y : C.ob} {f : C.hom x y}
            → {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
            → (fᴰ : hom[ f ] xᴰ yᴰ)
            → PathP (λ i → hom[ C.comp-hom-unit-right f i ] xᴰ yᴰ)
                (fᴰ ∙₁ᴰ id-homᴰ yᴰ)
                fᴰ

  record LocallyThinOver : Type (ℓ-max ℓC (ℓ-suc ℓCᴰ)) where
    field
      ob[_] : C.ob → Type ℓoᴰ
      hom[_] : {x y : C.ob} (f : C.hom x y) (xᴰ : ob[ x ]) (yᴰ : ob[ y ]) → Type ℓhᴰ
      rel[_] : {x y : C.ob} {f g : C.hom x y}
        → {xᴰ : ob[ x ]} → {yᴰ : ob[ y ]}
        → (s : C.rel f g)
        → (fᴰ : hom[ f ] xᴰ yᴰ)
        → (gᴰ : hom[ g ] xᴰ yᴰ)
        → Type ℓrᴰ

    field
      two-category-structureᴰ : TwoCategoryStrᴰ C _ _ _ ob[_] hom[_] rel[_]
      is-locally-thinᴰ : IsLocallyThinOver ob[_] hom[_] rel[_] two-category-structureᴰ

    open TwoCategoryStrᴰ two-category-structureᴰ public
    open IsLocallyThinOver is-locally-thinᴰ public

module TotalTwoCategory
  {ℓo ℓh ℓr} (C : TwoCategory ℓo ℓh ℓr)
  {ℓoᴰ ℓhᴰ ℓrᴰ : Level} (Cᴰ : LocallyThinOver C ℓoᴰ ℓhᴰ ℓrᴰ)
  where

  private
    open module C = TwoCategory C
    open module Cᴰ = LocallyThinOver Cᴰ

    ∫₀ : Type _
    ∫₀ = Σ ob ob[_]

    ∫₁ : (x y : ∫₀) → Type _
    ∫₁ (x , xᴰ) (y , yᴰ) = Σ[ f ∈ hom x y ] hom[ f ] xᴰ yᴰ

    ∫₂ : {x y : ∫₀} (f g : ∫₁ x y) → Type _
    ∫₂ (f , fᴰ) (g , gᴰ) = Σ[ r ∈ rel f g ] rel[ r ] fᴰ gᴰ

    ∫₁≡ : {x y : ∫₀} {f g : ∫₁ x y}
      → (base-path : f .fst ≡ g .fst)
      → (dep-path : PathP (λ i → hom[ base-path i ] (x .snd) (y .snd)) (f .snd) (g .snd))
      → f ≡ g
    ∫₁≡ base-path dep-path i .fst = base-path i
    ∫₁≡ base-path dep-path i .snd = dep-path i

  ∫₂≡ : {x y : ∫₀} {f g : ∫₁ x y} {r s : ∫₂ f g} → (r .fst ≡ s .fst) → r ≡ s
  ∫₂≡ = Σ≡Prop (λ r → is-prop-relᴰ _ _)

  ∫₂PathP : {x y : ∫₀}
    → {f₁ f₂ : ∫₁ x y} {g₁ g₂ : ∫₁ x y}
    → (pᶠ : f₁ ≡ f₂) (pᵍ : g₁ ≡ g₂)
    → {r : ∫₂ f₁ g₁} {s : ∫₂ f₂ g₂}
    → PathP (λ i → rel (pᶠ i .fst) (pᵍ i .fst)) (r .fst) (s .fst)
    → PathP (λ i → ∫₂ (pᶠ i) (pᵍ i)) r s
  ∫₂PathP pᶠ pᵍ base-path i .fst = base-path i
  ∫₂PathP pᶠ pᵍ {r} {s} base-path i .snd = isProp→PathP (λ i → is-prop-relᴰ {s = base-path i} (pᶠ i .snd) (pᵍ i .snd)) (r .snd) (s .snd) i

  ∫-two-category-structure : TwoCategoryStr ∫₀ ∫₁ ∫₂
  ∫-two-category-structure .TwoCategoryStr.id-hom (x , xᴰ) = id-hom x , id-homᴰ xᴰ
  ∫-two-category-structure .TwoCategoryStr.comp-hom (f , fᴰ) (g , gᴰ) = (f ∙₁ g) , fᴰ ∙₁ᴰ gᴰ
  ∫-two-category-structure .TwoCategoryStr.id-rel (f , fᴰ) = id-rel f , id-relᴰ fᴰ
  ∫-two-category-structure .TwoCategoryStr.trans (r , rᴰ) (s , sᴰ) = r ∙ᵥ s , rᴰ ∙ᵥᴰ sᴰ
  ∫-two-category-structure .TwoCategoryStr.comp-rel (r , rᴰ) (s , sᴰ) = r ∙ₕ s , rᴰ ∙ₕᴰ sᴰ

  ∫-is-two-cat : IsTwoCategory ∫₀ ∫₁ ∫₂ ∫-two-category-structure
  ∫-is-two-cat .IsTwoCategory.is-set-rel (f , fᴰ) (g , gᴰ) = isSetΣ (is-set-rel f g) λ r → isProp→isSet (is-prop-relᴰ fᴰ gᴰ)
  ∫-is-two-cat .IsTwoCategory.trans-assoc (r , _) (s , _) (t , _) = ∫₂≡ (trans-assoc r s t)
  ∫-is-two-cat .IsTwoCategory.trans-unit-left (r , _) = ∫₂≡ (trans-unit-left r)
  ∫-is-two-cat .IsTwoCategory.trans-unit-right (r , _) = ∫₂≡ (trans-unit-right r)
  ∫-is-two-cat .IsTwoCategory.comp-rel-id (f , _) (g , _) = ∫₂≡ (comp-rel-id f g)
  ∫-is-two-cat .IsTwoCategory.comp-rel-trans (s , _) (t , _) (u , _) (v , _) = ∫₂≡ (comp-rel-trans s t u v)
  ∫-is-two-cat .IsTwoCategory.comp-hom-assoc (f , fᴰ) (g , gᴰ) (h , hᴰ) = ∫₁≡ (comp-hom-assoc f g h) (comp-hom-assocᴰ fᴰ gᴰ hᴰ)
  ∫-is-two-cat .IsTwoCategory.comp-hom-unit-left (g , gᴰ) = ∫₁≡ (comp-hom-unit-left g) (comp-hom-unit-leftᴰ gᴰ)
  ∫-is-two-cat .IsTwoCategory.comp-hom-unit-right (f , fᴰ) = ∫₁≡ (comp-hom-unit-right f) (comp-hom-unit-rightᴰ fᴰ)
  ∫-is-two-cat .IsTwoCategory.comp-rel-assoc {f₁} {f₂} {g₁} {g₂} {k₁} {k₂} (s , _) (t , _) (u , _) =
    ∫₂PathP
      (∫-is-two-cat .IsTwoCategory.comp-hom-assoc f₁ g₁ k₁)
      (∫-is-two-cat .IsTwoCategory.comp-hom-assoc f₂ g₂ k₂)
      (comp-rel-assoc s t u)
  ∫-is-two-cat .IsTwoCategory.comp-rel-unit-left {f} {g} (s , _) =
    ∫₂PathP
      (∫-is-two-cat .IsTwoCategory.comp-hom-unit-left f)
      (∫-is-two-cat .IsTwoCategory.comp-hom-unit-left g)
      (comp-rel-unit-left s)
  ∫-is-two-cat .IsTwoCategory.comp-rel-unit-right {f} {g} (r , _) =
    ∫₂PathP
      (∫-is-two-cat .IsTwoCategory.comp-hom-unit-right f)
      (∫-is-two-cat .IsTwoCategory.comp-hom-unit-right g)
      (comp-rel-unit-right r)

  ∫ : TwoCategory (ℓ-max ℓo ℓoᴰ) (ℓ-max ℓh ℓhᴰ) (ℓ-max ℓr ℓrᴰ)
  ∫ .TwoCategory.ob = ∫₀
  ∫ .TwoCategory.hom = ∫₁
  ∫ .TwoCategory.rel = ∫₂
  ∫ .TwoCategory.two-category-structure = ∫-two-category-structure
  ∫ .TwoCategory.is-two-category = ∫-is-two-cat
