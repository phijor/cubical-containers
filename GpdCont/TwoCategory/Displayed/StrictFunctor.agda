module GpdCont.TwoCategory.Displayed.StrictFunctor where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.StrictFunctor
open import GpdCont.TwoCategory.Displayed.Base

open TotalTwoCategory using (∫)

module _
  {ℓoC ℓoCᴰ ℓoD ℓoDᴰ}
  {ℓhC ℓhCᴰ ℓhD ℓhDᴰ}
  {ℓrC ℓrCᴰ ℓrD ℓrDᴰ}
  {C : TwoCategory ℓoC ℓhC ℓrC}
  {D : TwoCategory ℓoD ℓhD ℓrD}
  (F : StrictFunctor C D)
  (Cᴰ : TwoCategoryᴰ C ℓoCᴰ ℓhCᴰ ℓrCᴰ)
  (Dᴰ : TwoCategoryᴰ D ℓoDᴰ ℓhDᴰ ℓrDᴰ)
  where
    private
      ℓ : Level
      ℓ = ℓMax ℓoC ℓoCᴰ ℓoD ℓoDᴰ ℓhC ℓhCᴰ ℓhD ℓhDᴰ ℓrC ℓrCᴰ ℓrD ℓrDᴰ
      module C = TwoCategory C
      module D = TwoCategory D
      open module F = StrictFunctor F hiding (₀ ; ₁ ; ₂)
      module Cᴰ = TwoCategoryᴰ Cᴰ
      module Dᴰ = TwoCategoryᴰ Dᴰ

    record StrictFunctorᴰ : Type ℓ where
      no-eta-equality

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
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
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

      -- ====================== --
      -- Strictness constraints --
      -- ====================== --
      field
        -- Strict functoriality
        -- ====================
        F-hom-compᴰ : {x y z : C.ob} {f : C.hom x y} {g : C.hom y z}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
          → (gᴰ : Cᴰ.hom[ g ] yᴰ zᴰ)
          → PathP (λ i → Dᴰ.hom[ F-hom-comp f g i ] (F-obᴰ xᴰ) (F-obᴰ zᴰ))
            (F-homᴰ fᴰ Dᴰ.∙₁ᴰ F-homᴰ gᴰ)
            (F-homᴰ (fᴰ Cᴰ.∙₁ᴰ gᴰ))

        F-hom-idᴰ : {x : C.ob} (xᴰ : Cᴰ.ob[ x ])
          → PathP (λ i → Dᴰ.hom[ F-hom-id x i ] (F-obᴰ xᴰ) (F-obᴰ xᴰ))
            (Dᴰ.id-homᴰ (F-obᴰ xᴰ))
            (F-homᴰ (Cᴰ.id-homᴰ xᴰ))

      field
        -- Strict associativity
        -- ====================
        F-assoc-filler-leftᴰ : {x y z w : C.ob}
          → {f : C.hom x y} {g : C.hom y z} {h : C.hom z w}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]} {wᴰ : Cᴰ.ob[ w ]}
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
          → (gᴰ : Cᴰ.hom[ g ] yᴰ zᴰ)
          → (hᴰ : Cᴰ.hom[ h ] zᴰ wᴰ)
          → DoubleCompPathPFiller
              (λ i j → Dᴰ.hom[ F-assoc-filler-left f g h .snd i j ] (F-obᴰ xᴰ) (F-obᴰ wᴰ))
              refl
              (λ i → F-hom-compᴰ fᴰ gᴰ i Dᴰ.∙₁ᴰ F-homᴰ hᴰ)
              (F-hom-compᴰ (fᴰ Cᴰ.∙₁ᴰ gᴰ) hᴰ)

        F-assoc-filler-rightᴰ : {x y z w : C.ob}
          → {f : C.hom x y} {g : C.hom y z} {h : C.hom z w}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]} {wᴰ : Cᴰ.ob[ w ]}
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
          → (gᴰ : Cᴰ.hom[ g ] yᴰ zᴰ)
          → (hᴰ : Cᴰ.hom[ h ] zᴰ wᴰ)
          → DoubleCompPathPFiller
              (λ i j → Dᴰ.hom[ F-assoc-filler-right f g h .snd i j ] (F-obᴰ xᴰ) (F-obᴰ wᴰ))
              refl
              (λ i → F-homᴰ fᴰ Dᴰ.∙₁ᴰ F-hom-compᴰ gᴰ hᴰ i)
              (F-hom-compᴰ fᴰ (gᴰ Cᴰ.∙₁ᴰ hᴰ))

        F-assocᴰ : {x y z w : C.ob}
          → {f : C.hom x y} {g : C.hom y z} {h : C.hom z w}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]} {wᴰ : Cᴰ.ob[ w ]}
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
          → (gᴰ : Cᴰ.hom[ g ] yᴰ zᴰ)
          → (hᴰ : Cᴰ.hom[ h ] zᴰ wᴰ)
          → SquareP (λ i j → Dᴰ.hom[ F-assoc f g h i j ] (F-obᴰ xᴰ) (F-obᴰ wᴰ))
              (F-assoc-filler-leftᴰ fᴰ gᴰ hᴰ .fst)
              (F-assoc-filler-rightᴰ fᴰ gᴰ hᴰ .fst)
              (Dᴰ.comp-hom-assocᴰ (F-homᴰ fᴰ) (F-homᴰ gᴰ) (F-homᴰ hᴰ))
              (λ i → F-homᴰ (Cᴰ.comp-hom-assocᴰ fᴰ gᴰ hᴰ i))

        -- Strict unitality
        -- ================
        F-unit-left-fillerᴰ : {x y : C.ob} {f : C.hom x y}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
          → DoubleCompPathPFiller
              (λ i j → Dᴰ.hom[ F-unit-left-filler f .snd i j ] (F-obᴰ xᴰ) (F-obᴰ yᴰ))
              refl
              (λ j → F-hom-idᴰ xᴰ j Dᴰ.∙₁ᴰ F-homᴰ fᴰ)
              (F-hom-compᴰ (Cᴰ.id-homᴰ xᴰ) fᴰ)

        F-unit-leftᴰ : {x y : C.ob} {f : C.hom x y}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
          → SquareP (λ i j → Dᴰ.hom[ F-unit-left f i j ] (F-obᴰ xᴰ) (F-obᴰ yᴰ))
              (F-unit-left-fillerᴰ fᴰ .fst)
              (refl′ (F-homᴰ fᴰ))
              (Dᴰ.comp-hom-unit-leftᴰ (F-homᴰ fᴰ))
              (λ i → F-homᴰ (Cᴰ.comp-hom-unit-leftᴰ fᴰ i))

        F-unit-right-fillerᴰ : {x y : C.ob} {f : C.hom x y}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
          → DoubleCompPathPFiller
              (λ i j → Dᴰ.hom[ F-unit-right-filler f .snd i j ] (F-obᴰ xᴰ) (F-obᴰ yᴰ))
              refl
              (λ j → F-homᴰ fᴰ Dᴰ.∙₁ᴰ F-hom-idᴰ yᴰ j)
              (F-hom-compᴰ fᴰ (Cᴰ.id-homᴰ yᴰ))

        F-unit-rightᴰ : {x y : C.ob} {f : C.hom x y}
          → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
          → (fᴰ : Cᴰ.hom[ f ] xᴰ yᴰ)
          → SquareP (λ i j → Dᴰ.hom[ F-unit-right f i j ] (F-obᴰ xᴰ) (F-obᴰ yᴰ))
              (F-unit-right-fillerᴰ fᴰ .fst)
              (refl′ (F-homᴰ fᴰ))
              (Dᴰ.comp-hom-unit-rightᴰ (F-homᴰ fᴰ))
              (λ i → F-homᴰ (Cᴰ.comp-hom-unit-rightᴰ fᴰ i))

      toTotalFunctor : StrictFunctor (∫ C Cᴰ) (∫ D Dᴰ)
      toTotalFunctor .StrictFunctor.F-ob (x , xᴰ) .fst = F-ob x
      toTotalFunctor .StrictFunctor.F-ob (x , xᴰ) .snd = F-obᴰ xᴰ
      toTotalFunctor .StrictFunctor.F-hom (f , fᴰ) .fst = F-hom f
      toTotalFunctor .StrictFunctor.F-hom (f , fᴰ) .snd = F-homᴰ fᴰ
      toTotalFunctor .StrictFunctor.F-rel (r , rᴰ) .fst = F-rel r
      toTotalFunctor .StrictFunctor.F-rel (r , rᴰ) .snd = F-relᴰ rᴰ
      toTotalFunctor .StrictFunctor.F-rel-id {f = f , fᴰ} i .fst = F-rel-id {f = f} i
      toTotalFunctor .StrictFunctor.F-rel-id {f = f , fᴰ} i .snd = F-rel-idᴰ fᴰ i
      toTotalFunctor .StrictFunctor.F-rel-trans (r , rᴰ) (s , sᴰ) i .fst = F-rel-trans r s i
      toTotalFunctor .StrictFunctor.F-rel-trans (r , rᴰ) (s , sᴰ) i .snd = F-rel-transᴰ rᴰ sᴰ i
      toTotalFunctor .StrictFunctor.F-hom-comp (f , fᴰ) (g , gᴰ) i .fst = F-hom-comp f g i
      toTotalFunctor .StrictFunctor.F-hom-comp (f , fᴰ) (g , gᴰ) i .snd = F-hom-compᴰ fᴰ gᴰ i
      toTotalFunctor .StrictFunctor.F-hom-id (x , xᴰ) i .fst = F-hom-id x i
      toTotalFunctor .StrictFunctor.F-hom-id (x , xᴰ) i .snd = F-hom-idᴰ xᴰ i
      toTotalFunctor .StrictFunctor.F-assoc-filler-left (f , fᴰ) (g , gᴰ) (h , hᴰ) .fst i .fst = F-assoc-filler-left f g h .fst i
      toTotalFunctor .StrictFunctor.F-assoc-filler-left (f , fᴰ) (g , gᴰ) (h , hᴰ) .fst i .snd = F-assoc-filler-leftᴰ fᴰ gᴰ hᴰ .fst i
      toTotalFunctor .StrictFunctor.F-assoc-filler-left (f , fᴰ) (g , gᴰ) (h , hᴰ) .snd i j .fst = F-assoc-filler-left f g h .snd i j
      toTotalFunctor .StrictFunctor.F-assoc-filler-left (f , fᴰ) (g , gᴰ) (h , hᴰ) .snd i j .snd = F-assoc-filler-leftᴰ fᴰ gᴰ hᴰ .snd i j
      toTotalFunctor .StrictFunctor.F-assoc-filler-right (f , fᴰ) (g , gᴰ) (h , hᴰ) .fst i .fst = F-assoc-filler-right f g h .fst i
      toTotalFunctor .StrictFunctor.F-assoc-filler-right (f , fᴰ) (g , gᴰ) (h , hᴰ) .fst i .snd = F-assoc-filler-rightᴰ fᴰ gᴰ hᴰ .fst i
      toTotalFunctor .StrictFunctor.F-assoc-filler-right (f , fᴰ) (g , gᴰ) (h , hᴰ) .snd i j .fst = F-assoc-filler-right f g h .snd i j
      toTotalFunctor .StrictFunctor.F-assoc-filler-right (f , fᴰ) (g , gᴰ) (h , hᴰ) .snd i j .snd = F-assoc-filler-rightᴰ fᴰ gᴰ hᴰ .snd i j
      toTotalFunctor .StrictFunctor.F-assoc (f , fᴰ) (g , gᴰ) (h , hᴰ) i j .fst = F-assoc f g h i j
      toTotalFunctor .StrictFunctor.F-assoc (f , fᴰ) (g , gᴰ) (h , hᴰ) i j .snd = F-assocᴰ fᴰ gᴰ hᴰ i j
      toTotalFunctor .StrictFunctor.F-unit-left-filler (f , fᴰ) .fst i .fst = F-unit-left-filler f .fst i
      toTotalFunctor .StrictFunctor.F-unit-left-filler (f , fᴰ) .fst i .snd = F-unit-left-fillerᴰ fᴰ .fst i
      toTotalFunctor .StrictFunctor.F-unit-left-filler (f , fᴰ) .snd i j .fst = F-unit-left-filler f .snd i j
      toTotalFunctor .StrictFunctor.F-unit-left-filler (f , fᴰ) .snd i j .snd = F-unit-left-fillerᴰ fᴰ .snd i j
      toTotalFunctor .StrictFunctor.F-unit-left (f , fᴰ) i j .fst = F-unit-left f i j
      toTotalFunctor .StrictFunctor.F-unit-left (f , fᴰ) i j .snd = F-unit-leftᴰ fᴰ i j
      toTotalFunctor .StrictFunctor.F-unit-right-filler (f , fᴰ) .fst i .fst = F-unit-right-filler f .fst i
      toTotalFunctor .StrictFunctor.F-unit-right-filler (f , fᴰ) .fst i .snd = F-unit-right-fillerᴰ fᴰ .fst i
      toTotalFunctor .StrictFunctor.F-unit-right-filler (f , fᴰ) .snd i j .fst = F-unit-right-filler f .snd i j
      toTotalFunctor .StrictFunctor.F-unit-right-filler (f , fᴰ) .snd i j .snd = F-unit-right-fillerᴰ fᴰ .snd i j
      toTotalFunctor .StrictFunctor.F-unit-right (f , fᴰ) i j .fst = F-unit-right f i j
      toTotalFunctor .StrictFunctor.F-unit-right (f , fᴰ) i j .snd = F-unit-rightᴰ fᴰ i j
