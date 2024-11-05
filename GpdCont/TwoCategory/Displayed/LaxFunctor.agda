module GpdCont.TwoCategory.Displayed.LaxFunctor where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.Displayed.Base

open TotalTwoCategory using (∫)

module _
  {ℓoC ℓoCᴰ ℓoD ℓoDᴰ}
  {ℓhC ℓhCᴰ ℓhD ℓhDᴰ}
  {ℓrC ℓrCᴰ ℓrD ℓrDᴰ}
  {C : TwoCategory ℓoC ℓhC ℓrC}
  {D : TwoCategory ℓoD ℓhD ℓrD}
  (F : LaxFunctor C D)
  (Cᴰ : TwoCategoryᴰ C ℓoCᴰ ℓhCᴰ ℓrCᴰ)
  (Dᴰ : TwoCategoryᴰ D ℓoDᴰ ℓhDᴰ ℓrDᴰ)
  where
    private
      ℓ : Level
      ℓ = ℓMax ℓoC ℓoCᴰ ℓoD ℓoDᴰ ℓhC ℓhCᴰ ℓhD ℓhDᴰ ℓrC ℓrCᴰ ℓrD ℓrDᴰ
      module C = TwoCategory C
      module D = TwoCategory D
      open module F = LaxFunctor F hiding (₀ ; ₁ ; ₂)
      module Cᴰ = TwoCategoryᴰ Cᴰ
      module Dᴰ = TwoCategoryᴰ Dᴰ

    record LaxFunctorᴰ : Type ℓ where
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

      -- F-homᴰ is a displayed functor of local categories over F-hom
      field
        F-rel-idᴰ : {x y : C.ob} {f : C.hom x y}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
          → {fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ}
          → PathP (λ i → Dᴰ.rel[ F-rel-id {f = f} i ] (F-homᴰ fᴰ) (F-homᴰ fᴰ))
            (F-relᴰ (Cᴰ.id-relᴰ fᴰ))
            (Dᴰ.id-relᴰ (F-homᴰ fᴰ))
        F-rel-transᴰ : {x y : C.ob} {f g h : C.hom x y} {r : C.rel f g} {s : C.rel g h}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
          → {fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ}
          → {gᴰ : Cᴰ.hom[ g ] xᴰ yᴰ}
          → {hᴰ : Cᴰ.hom[ h ] xᴰ yᴰ}
          → (rᴰ : Cᴰ.rel[ r ] fᴰ gᴰ)
          → (sᴰ : Cᴰ.rel[ s ] gᴰ hᴰ)
          → PathP (λ i → Dᴰ.rel[ F-rel-trans r s i ] (F-homᴰ fᴰ) (F-homᴰ hᴰ))
            (F-relᴰ (rᴰ Cᴰ.∙ᵥᴰ sᴰ))
            ((F-relᴰ rᴰ) Dᴰ.∙ᵥᴰ (F-relᴰ sᴰ))

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

        F-trans-lax-naturalᴰ : {x y z : C.ob} {f₁ f₂ : C.hom x y} {g₁ g₂ : C.hom y z} {r : C.rel f₁ f₂} {s : C.rel g₁ g₂}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
          → {f₁ᴰ : Cᴰ.hom[ f₁ ] xᴰ yᴰ}
          → {f₂ᴰ : Cᴰ.hom[ f₂ ] xᴰ yᴰ}
          → {g₁ᴰ : Cᴰ.hom[ g₁ ] yᴰ zᴰ}
          → {g₂ᴰ : Cᴰ.hom[ g₂ ] yᴰ zᴰ}
          → (rᴰ : Cᴰ.rel[ r ] f₁ᴰ f₂ᴰ)
          → (sᴰ : Cᴰ.rel[ s ] g₁ᴰ g₂ᴰ)
          → PathP (λ i → Dᴰ.rel[ F-trans-lax-natural r s i ] ((F-homᴰ f₁ᴰ) Dᴰ.∙₁ᴰ (F-homᴰ g₁ᴰ)) (F-homᴰ (f₂ᴰ Cᴰ.∙₁ᴰ g₂ᴰ)))
            ((F-relᴰ rᴰ Dᴰ.∙ₕᴰ F-relᴰ sᴰ) Dᴰ.∙ᵥᴰ (F-trans-laxᴰ f₂ᴰ g₂ᴰ))
            (F-trans-laxᴰ f₁ᴰ g₁ᴰ Dᴰ.∙ᵥᴰ F-relᴰ (rᴰ Cᴰ.∙ₕᴰ sᴰ))

        F-id-laxᴰ : {x : C.ob} (xᴰ : Cᴰ.ob[ x ])
          → Dᴰ.rel[ F-id-lax x ] (Dᴰ.id-homᴰ (F-obᴰ xᴰ)) (F-homᴰ (Cᴰ.id-homᴰ xᴰ))

      field
        -- Lax associativity of displayed 1-cells
        F-assocᴰ : {x y z w : C.ob} {f : C.hom x y} {g : C.hom y z} {h : C.hom z w}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]} {wᴰ : Cᴰ.ob[ w ]}
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
          → (gᴰ : Cᴰ.hom[ g ] yᴰ zᴰ)
          → (hᴰ : Cᴰ.hom[ h ] zᴰ wᴰ)
          → PathP (λ i → Dᴰ.rel[ F-assoc f g h i ] (Dᴰ.comp-hom-assocᴰ (F-homᴰ fᴰ) (F-homᴰ gᴰ) (F-homᴰ hᴰ) i) (F-homᴰ (Cᴰ.comp-hom-assocᴰ fᴰ gᴰ hᴰ i)))
              ((F-trans-laxᴰ fᴰ gᴰ Dᴰ.∙ₕᴰ Dᴰ.id-relᴰ (F-homᴰ hᴰ)) Dᴰ.∙ᵥᴰ F-trans-laxᴰ (fᴰ Cᴰ.∙₁ᴰ gᴰ) hᴰ)
              ((Dᴰ.id-relᴰ (F-homᴰ fᴰ) Dᴰ.∙ₕᴰ F-trans-laxᴰ gᴰ hᴰ) Dᴰ.∙ᵥᴰ F-trans-laxᴰ fᴰ (gᴰ Cᴰ.∙₁ᴰ hᴰ))

        F-unit-leftᴰ : {x y : C.ob} {f : C.hom x y} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
          → PathP (λ i → Dᴰ.rel[ F-unit-left f i ] (Dᴰ.comp-hom-unit-leftᴰ (F-homᴰ fᴰ) i) (F-homᴰ (Cᴰ.comp-hom-unit-leftᴰ fᴰ i)))
              ((F-id-laxᴰ xᴰ Dᴰ.∙ₕᴰ Dᴰ.id-relᴰ (F-homᴰ fᴰ)) Dᴰ.∙ᵥᴰ F-trans-laxᴰ (Cᴰ.id-homᴰ xᴰ) fᴰ)
              (Dᴰ.id-relᴰ (F-homᴰ fᴰ))

        F-unit-rightᴰ : {x y : C.ob} {f : C.hom x y} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
          → PathP (λ i → Dᴰ.rel[ F-unit-right f i ] (Dᴰ.comp-hom-unit-rightᴰ (F-homᴰ fᴰ) i) (F-homᴰ (Cᴰ.comp-hom-unit-rightᴰ fᴰ i)))
              ((Dᴰ.id-relᴰ (F-homᴰ fᴰ) Dᴰ.∙ₕᴰ F-id-laxᴰ yᴰ) Dᴰ.∙ᵥᴰ F-trans-laxᴰ fᴰ (Cᴰ.id-homᴰ yᴰ))
              (Dᴰ.id-relᴰ (F-homᴰ fᴰ))

      toTotalFunctor : LaxFunctor (∫ C Cᴰ) (∫ D Dᴰ)
      toTotalFunctor .LaxFunctor.F-ob (x , xᴰ) .fst = F-ob x
      toTotalFunctor .LaxFunctor.F-ob (x , xᴰ) .snd = F-obᴰ xᴰ
      toTotalFunctor .LaxFunctor.F-hom (f , fᴰ) .fst = F-hom f
      toTotalFunctor .LaxFunctor.F-hom (f , fᴰ) .snd = F-homᴰ fᴰ
      toTotalFunctor .LaxFunctor.F-rel (r , rᴰ) .fst = F-rel r
      toTotalFunctor .LaxFunctor.F-rel (r , rᴰ) .snd = F-relᴰ rᴰ
      toTotalFunctor .LaxFunctor.F-rel-id i .fst = F-rel-id i
      toTotalFunctor .LaxFunctor.F-rel-id i .snd = F-rel-idᴰ i
      toTotalFunctor .LaxFunctor.F-rel-trans (r , rᴰ) (s , sᴰ) i .fst = F-rel-trans r s i
      toTotalFunctor .LaxFunctor.F-rel-trans (r , rᴰ) (s , sᴰ) i .snd = F-rel-transᴰ rᴰ sᴰ i
      toTotalFunctor .LaxFunctor.F-trans-lax (f , fᴰ) (g , gᴰ) .fst = F-trans-lax f g
      toTotalFunctor .LaxFunctor.F-trans-lax (f , fᴰ) (g , gᴰ) .snd = F-trans-laxᴰ fᴰ gᴰ
      toTotalFunctor .LaxFunctor.F-trans-lax-natural (r , rᴰ) (s , sᴰ) i .fst = F-trans-lax-natural r s i
      toTotalFunctor .LaxFunctor.F-trans-lax-natural (r , rᴰ) (s , sᴰ) i .snd = F-trans-lax-naturalᴰ rᴰ sᴰ i
      toTotalFunctor .LaxFunctor.F-id-lax (x , xᴰ) .fst = F-id-lax x
      toTotalFunctor .LaxFunctor.F-id-lax (x , xᴰ) .snd = F-id-laxᴰ xᴰ
      toTotalFunctor .LaxFunctor.F-assoc (f , fᴰ) (g , gᴰ) (h , hᴰ) i .fst = F-assoc f g h i
      toTotalFunctor .LaxFunctor.F-assoc (f , fᴰ) (g , gᴰ) (h , hᴰ) i .snd = F-assocᴰ fᴰ gᴰ hᴰ i
      toTotalFunctor .LaxFunctor.F-unit-left (f , fᴰ) i .fst = F-unit-left f i
      toTotalFunctor .LaxFunctor.F-unit-left (f , fᴰ) i .snd = F-unit-leftᴰ fᴰ i
      toTotalFunctor .LaxFunctor.F-unit-right (f , fᴰ) i .fst = F-unit-right f i
      toTotalFunctor .LaxFunctor.F-unit-right (f , fᴰ) i .snd = F-unit-rightᴰ fᴰ i
