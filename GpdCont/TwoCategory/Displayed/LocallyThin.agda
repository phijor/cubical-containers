module GpdCont.TwoCategory.Displayed.LocallyThin where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LaxFunctor using (LaxFunctor)
open import GpdCont.TwoCategory.Displayed.Base as Disp hiding (module TotalTwoCategory)
open import GpdCont.TwoCategory.Displayed.LaxFunctor using (LaxFunctorᴰ)

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

        -- Any pair displayed 2-cells are connected by a path.
        -- Taking all possible dependencies in the base into account,
        -- this is the generic path lemma that we end up with:
        relᴰPathP : {x y : C.ob}
          → {f₀ f₁ : C.hom x y} → {f : PathP (λ i → C.hom x y) f₀ f₁}
          → {g₀ g₁ : C.hom x y} → {g : PathP (λ i → C.hom x y) g₀ g₁}
          → {r : C.rel f₀ g₀}
          → {s : C.rel f₁ g₁}
          → {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
          → {fᴰ₀ : hom[ f₀ ] xᴰ yᴰ} → {fᴰ₁ : hom[ f₁ ] xᴰ yᴰ} → {fᴰ : PathP (λ i → hom[ f i ] xᴰ yᴰ) fᴰ₀  fᴰ₁}
          → {gᴰ₀ : hom[ g₀ ] xᴰ yᴰ} → {gᴰ₁ : hom[ g₁ ] xᴰ yᴰ} → {gᴰ : PathP (λ i → hom[ g i ] xᴰ yᴰ) gᴰ₀  gᴰ₁}
          → {rᴰ : rel[ r ] fᴰ₀ gᴰ₀}
          → {sᴰ : rel[ s ] fᴰ₁ gᴰ₁}
          → (p : PathP (λ i → rel (f i) (g i)) r s)
          → PathP (λ i → rel[ p i ] (fᴰ i) (gᴰ i)) rᴰ sᴰ
        relᴰPathP {fᴰ} {gᴰ} {rᴰ} {sᴰ} p = isProp→PathP (λ i → is-prop-relᴰ {s = p i} (fᴰ i) (gᴰ i)) rᴰ sᴰ

        -- When the identification of 2-cells in the base is non-dependent,
        -- the type simplifies significantly, and we recognize that it actually
        -- identifies parallel displayed 2-cells rᴰ and sᴰ:
        relᴰ≡ : {x y : C.ob} {f g : C.hom x y} {r s : C.rel f g}
          → {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
          → {fᴰ : hom[ f ] xᴰ yᴰ}
          → {gᴰ : hom[ g ] xᴰ yᴰ}
          → {rᴰ : rel[ r ] fᴰ gᴰ}
          → {sᴰ : rel[ s ] fᴰ gᴰ}
          → (p : r ≡ s)
          → PathP (λ i → rel[ p i ] fᴰ gᴰ) rᴰ sᴰ
        relᴰ≡ = relᴰPathP

        toIsTwoCategoryᴰ : IsTwoCategoryᴰ C _ _ _ ob[_] hom[_] rel[_] sᴰ
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.is-set-relᴰ fᴰ gᴰ = isProp→isSet $ is-prop-relᴰ fᴰ gᴰ
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.trans-assocᴰ _ _ _ = relᴰ≡ (C.trans-assoc _ _ _)
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.trans-unit-leftᴰ _ = relᴰ≡ (C.trans-unit-left _)
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.trans-unit-rightᴰ _ = relᴰ≡ (C.trans-unit-right _)
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-rel-idᴰ _ _ = relᴰPathP _
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-rel-transᴰ _ _ _ _ = relᴰPathP _
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-hom-assocᴰ = comp-hom-assocᴰ
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-hom-unit-leftᴰ = comp-hom-unit-leftᴰ
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-hom-unit-rightᴰ = comp-hom-unit-rightᴰ
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-rel-assocᴰ {s} {t} {u} _ _ _ = relᴰPathP (comp-rel-assoc s t u)
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-rel-unit-leftᴰ {s} _ = relᴰPathP (comp-rel-unit-left s)
        toIsTwoCategoryᴰ .IsTwoCategoryᴰ.comp-rel-unit-rightᴰ {r} _ = relᴰPathP (comp-rel-unit-right r)

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


-- For defining lax functors into locally thin displayed 2-categories,
-- one can get away with verifying a lot less properties: one needs to
-- provide the usual stuff (actions on {0,1,2}-cells) and data of the
-- laxity constraints.
--
-- All other properties are (dependendent) paths between 2-cells, and
-- those always exists, since the target 2-cells are propositons>
--
-- `IntoLocallyThin` contains the data of a functor into some locally thin `Dᴰ`.
module _
  {ℓoC ℓoCᴰ ℓoD ℓoDᴰ}
  {ℓhC ℓhCᴰ ℓhD ℓhDᴰ}
  {ℓrC ℓrCᴰ ℓrD ℓrDᴰ}
  {C : TwoCategory ℓoC ℓhC ℓrC}
  {D : TwoCategory ℓoD ℓhD ℓrD}
  (F : LaxFunctor C D)
  (Cᴰ : TwoCategoryᴰ C ℓoCᴰ ℓhCᴰ ℓrCᴰ)
  (Dᴰ : LocallyThinOver D ℓoDᴰ ℓhDᴰ ℓrDᴰ)
  where
    private
      ℓ : Level
      ℓ = ℓMax ℓoC ℓoCᴰ ℓoD ℓoDᴰ ℓhC ℓhCᴰ ℓhD ℓhDᴰ ℓrC ℓrCᴰ ℓrD ℓrDᴰ
      module C = TwoCategory C
      module D = TwoCategory D
      open module F = LaxFunctor F hiding (₀ ; ₁ ; ₂)
      module Cᴰ = TwoCategoryᴰ Cᴰ
      module Dᴰ = LocallyThinOver Dᴰ

    record IntoLocallyThin : Type ℓ where
      field
        F-obᴰ : {x : C.ob}
          → Cᴰ.ob[ x ] → Dᴰ.ob[ F.₀ x ]
        F-homᴰ : {x y : C.ob} {f : C.hom x y}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
          → Cᴰ.hom[ f ] xᴰ yᴰ → Dᴰ.hom[ F.₁ f ] (F-obᴰ xᴰ) (F-obᴰ yᴰ)
        F-relᴰ : {x y : C.ob} {f g : C.hom x y} {r : C.rel f g}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
          → {fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ}
          → {gᴰ : Cᴰ.hom[ g ] xᴰ yᴰ}
          → Cᴰ.rel[ r ] fᴰ gᴰ → Dᴰ.rel[ F.₂ r ] (F-homᴰ fᴰ) (F-homᴰ gᴰ)

      ₀ = F-obᴰ
      ₁ = F-homᴰ
      ₂ = F-relᴰ

      -- Displayed laxity constraints
      field
        -- Lax functoriality
        F-trans-laxᴰ : {x y z : C.ob} {f : C.hom x y} {g : C.hom y z}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
          → (gᴰ : Cᴰ.hom[ g ] yᴰ zᴰ)
          → Dᴰ.rel[ F-trans-lax f g ]
            ((F-homᴰ fᴰ) Dᴰ.∙₁ᴰ (F-homᴰ gᴰ))
            (F-homᴰ (fᴰ Cᴰ.∙₁ᴰ gᴰ))

        F-id-laxᴰ : {x : C.ob} (xᴰ : Cᴰ.ob[ x ])
          → Dᴰ.rel[ F-id-lax x ] (Dᴰ.id-homᴰ (F-obᴰ xᴰ)) (F-homᴰ (Cᴰ.id-homᴰ xᴰ))

      -- The induced displayed functor has all of its coherence conditions on 2-cells
      -- satisfied by the path lemma in Dᴰ: parallel displayed 2-cells are identical.
      toLaxFunctorᴰ : LaxFunctorᴰ F Cᴰ (Dᴰ.toTwoCategoryᴰ)
      toLaxFunctorᴰ .LaxFunctorᴰ.F-obᴰ = F-obᴰ
      toLaxFunctorᴰ .LaxFunctorᴰ.F-homᴰ = F-homᴰ
      toLaxFunctorᴰ .LaxFunctorᴰ.F-relᴰ = F-relᴰ
      toLaxFunctorᴰ .LaxFunctorᴰ.F-rel-idᴰ = Dᴰ.relᴰ≡ F-rel-id
      toLaxFunctorᴰ .LaxFunctorᴰ.F-rel-transᴰ _ _ = Dᴰ.relᴰ≡ (F-rel-trans _ _)
      toLaxFunctorᴰ .LaxFunctorᴰ.F-trans-laxᴰ = F-trans-laxᴰ
      toLaxFunctorᴰ .LaxFunctorᴰ.F-trans-lax-naturalᴰ _ _ = Dᴰ.relᴰ≡ (F-trans-lax-natural _ _)
      toLaxFunctorᴰ .LaxFunctorᴰ.F-id-laxᴰ = F-id-laxᴰ
      toLaxFunctorᴰ .LaxFunctorᴰ.F-assocᴰ _ _ _ = Dᴰ.relᴰPathP (F-assoc _ _ _)
      toLaxFunctorᴰ .LaxFunctorᴰ.F-unit-leftᴰ _ = Dᴰ.relᴰPathP (F-unit-left _)
      toLaxFunctorᴰ .LaxFunctorᴰ.F-unit-rightᴰ _ = Dᴰ.relᴰPathP (F-unit-right _)
