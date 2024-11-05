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

        relᴰPathP : {x y : C.ob} {f g : C.hom x y} {r s : C.rel f g}
          → {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
          → {fᴰ : hom[ f ] xᴰ yᴰ}
          → {gᴰ : hom[ g ] xᴰ yᴰ}
          → {rᴰ : rel[ r ] fᴰ gᴰ}
          → {sᴰ : rel[ s ] fᴰ gᴰ}
          → (p : r ≡ s)
          → PathP (λ i → rel[ p i ] fᴰ gᴰ) rᴰ sᴰ
        relᴰPathP p = isProp→PathP (λ i → is-prop-relᴰ {s = p i} _ _) _ _

        toIsTwoCategoryᴰ : IsTwoCategoryᴰ C _ _ _ ob[_] hom[_] rel[_] sᴰ
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.is-set-relᴰ fᴰ gᴰ = isProp→isSet $ is-prop-relᴰ fᴰ gᴰ
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.trans-assocᴰ _ _ _ = relᴰPathP _
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.trans-unit-leftᴰ _ = relᴰPathP _
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.trans-unit-rightᴰ _ = relᴰPathP _
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-rel-idᴰ _ _ = relᴰPathP _
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-rel-transᴰ _ _ _ _ = relᴰPathP _
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-hom-assocᴰ = comp-hom-assocᴰ
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-hom-unit-leftᴰ = comp-hom-unit-leftᴰ
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-hom-unit-rightᴰ = comp-hom-unit-rightᴰ
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-rel-assocᴰ {s} {t} {u} _ _ _ =
          isProp→PathP (λ i → is-prop-relᴰ {s = comp-rel-assoc s t u i} (comp-hom-assocᴰ _ _ _ i) (comp-hom-assocᴰ _ _ _ i)) _ _
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-rel-unit-leftᴰ {s} {fᴰ} {gᴰ} _ =
          isProp→PathP (λ i → is-prop-relᴰ {s = comp-rel-unit-left s i} (comp-hom-unit-leftᴰ fᴰ i) (comp-hom-unit-leftᴰ gᴰ i)) _ _
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-rel-unit-rightᴰ {r} {fᴰ} {gᴰ} _ =
          isProp→PathP (λ i → is-prop-relᴰ {s = comp-rel-unit-right r i} (comp-hom-unit-rightᴰ fᴰ i) (comp-hom-unit-rightᴰ gᴰ i)) _ _

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

    toTwoCategoryᴰ : Disp.TwoCategoryᴰ C _ _ _
    toTwoCategoryᴰ .TwoCategoryᴰ.ob[_] = ob[_]
    toTwoCategoryᴰ .TwoCategoryᴰ.hom[_] = hom[_]
    toTwoCategoryᴰ .TwoCategoryᴰ.rel[_] = rel[_]
    toTwoCategoryᴰ .TwoCategoryᴰ.two-category-structureᴰ = two-category-structureᴰ
    toTwoCategoryᴰ .TwoCategoryᴰ.is-two-categoryᴰ = toIsTwoCategoryᴰ

module TotalTwoCategory
  {ℓo ℓh ℓr} (C : TwoCategory ℓo ℓh ℓr)
  {ℓoᴰ ℓhᴰ ℓrᴰ : Level} (Cᴰ : LocallyThinOver C ℓoᴰ ℓhᴰ ℓrᴰ)
  where

  private
    open module C = TwoCategory C
    open module Cᴰ = LocallyThinOver Cᴰ

  ∫ : TwoCategory (ℓ-max ℓo ℓoᴰ) (ℓ-max ℓh ℓhᴰ) (ℓ-max ℓr ℓrᴰ)
  ∫ = Disp.TotalTwoCategory.∫ C toTwoCategoryᴰ
