module GpdCont.TwoCategory.Displayed.Base where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (Σ≡Prop)

module _ {ℓo ℓh ℓr} (C : TwoCategory ℓo ℓh ℓr) (ℓoᴰ ℓhᴰ ℓrᴰ : Level) where
  private
    ℓC = ℓ-of C
    ℓCᴰ = ℓMax (ℓoᴰ , ℓhᴰ , ℓrᴰ)
    module C = TwoCategory C

    variable
      x y z : C.ob
      f : C.hom x y
      g : C.hom y z

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
      record TwoCategoryStrᴰ : Type (ℓ-max ℓC ℓCᴰ) where
        field
          id-homᴰ : (xᴰ : ob[ x ]) → hom[ id-hom x ] xᴰ xᴰ
          comp-homᴰ : {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
            → (fᴰ : hom[ f ] xᴰ yᴰ)
            → (gᴰ : hom[ g ] yᴰ zᴰ)
            → hom[ comp-hom f g ] xᴰ zᴰ

        field
          id-relᴰ : {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
            → (fᴰ : hom[ f ] xᴰ yᴰ)
            → rel[ id-rel f ] fᴰ fᴰ

          transᴰ : {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
            → {f g h : hom x y}
            → {r : rel f g}
            → {s : rel g h}
            → {fᴰ : hom[ f ] xᴰ yᴰ}
            → {gᴰ : hom[ g ] xᴰ yᴰ}
            → {hᴰ : hom[ h ] xᴰ yᴰ}
            → (rᴰ : rel[ r ] fᴰ gᴰ)
            → (sᴰ : rel[ s ] gᴰ hᴰ)
            → rel[ trans r s ] fᴰ hᴰ

          comp-relᴰ : {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
            → {f₁ f₂ : hom x y}
            → {g₁ g₂ : hom y z}
            → {r : rel f₁ f₂}
            → {s : rel g₁ g₂}
            → {f₁ᴰ : hom[ f₁ ] xᴰ yᴰ}
            → {f₂ᴰ : hom[ f₂ ] xᴰ yᴰ}
            → {g₁ᴰ : hom[ g₁ ] yᴰ zᴰ}
            → {g₂ᴰ : hom[ g₂ ] yᴰ zᴰ}
            → (rᴰ : rel[ r ] f₁ᴰ f₂ᴰ)
            → (sᴰ : rel[ s ] g₁ᴰ g₂ᴰ)
            → rel[ comp-rel r s ] (comp-homᴰ f₁ᴰ g₁ᴰ) (comp-homᴰ f₂ᴰ g₂ᴰ)

        _∙₁ᴰ_ = comp-homᴰ
        _∙ᵥᴰ_ = transᴰ
        _∙ₕᴰ_ = comp-relᴰ

      record IsTwoCategoryᴰ (sᴰ : TwoCategoryStrᴰ) : Type (ℓ-max ℓC ℓCᴰ) where
        private
          open module sᴰ = TwoCategoryStrᴰ sᴰ

        field
          is-set-relᴰ : {x y : ob} {f g : hom x y} {s : rel f g}
            → {xᴰ : ob[ x ]}
            → {yᴰ : ob[ y ]}
            → (fᴰ : hom[ f ] xᴰ yᴰ)
            → (gᴰ : hom[ g ] xᴰ yᴰ)
            → isSet (rel[ s ] fᴰ gᴰ)

        field
          trans-assocᴰ : {x y : ob}
            → {f g h k : hom x y}
            → {r : rel f g}
            → {s : rel g h}
            → {t : rel h k}
            → {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
            → {fᴰ : hom[ f ] xᴰ yᴰ}
            → {gᴰ : hom[ g ] xᴰ yᴰ}
            → {hᴰ : hom[ h ] xᴰ yᴰ}
            → {kᴰ : hom[ k ] xᴰ yᴰ}
            → (rᴰ : rel[ r ] fᴰ gᴰ)
            → (sᴰ : rel[ s ] gᴰ hᴰ)
            → (tᴰ : rel[ t ] hᴰ kᴰ)
            → PathP (λ i → rel[ trans-assoc r s t i ] fᴰ kᴰ)
              ((rᴰ ∙ᵥᴰ sᴰ) ∙ᵥᴰ tᴰ)
              (rᴰ ∙ᵥᴰ (sᴰ ∙ᵥᴰ tᴰ))
          
          trans-unit-leftᴰ : {x y : ob}
            → {f g : hom x y}
            → {s : rel f g}
            → {xᴰ : ob[ x ]}
            → {yᴰ : ob[ y ]}
            → {fᴰ : hom[ f ] xᴰ yᴰ}
            → {gᴰ : hom[ g ] xᴰ yᴰ}
            → (sᴰ : rel[ s ] fᴰ gᴰ)
            → PathP (λ i → rel[ trans-unit-left s i ] fᴰ gᴰ)
              (id-relᴰ fᴰ ∙ᵥᴰ sᴰ)
              sᴰ

          trans-unit-rightᴰ : {x y : ob}
            → {f g : hom x y}
            → {r : rel f g}
            → {xᴰ : ob[ x ]}
            → {yᴰ : ob[ y ]}
            → {fᴰ : hom[ f ] xᴰ yᴰ}
            → {gᴰ : hom[ g ] xᴰ yᴰ}
            → (rᴰ : rel[ r ] fᴰ gᴰ)
            → PathP (λ i → rel[ trans-unit-right r i ] fᴰ gᴰ)
              (rᴰ ∙ᵥᴰ id-relᴰ gᴰ)
              rᴰ

        field
          comp-rel-idᴰ : {x y z : ob} {f : hom x y} {g : hom y z}
            → {xᴰ : ob[ x ]}
            → {yᴰ : ob[ y ]}
            → {zᴰ : ob[ z ]}
            → (fᴰ : hom[ f ] xᴰ yᴰ)
            → (gᴰ : hom[ g ] yᴰ zᴰ)
            → PathP (λ i → rel[ comp-rel-id f g i ] (fᴰ ∙₁ᴰ gᴰ) (fᴰ ∙₁ᴰ gᴰ))
              (id-relᴰ (fᴰ ∙₁ᴰ gᴰ))
              (id-relᴰ fᴰ ∙ₕᴰ id-relᴰ gᴰ)

          comp-rel-transᴰ : {x y z : ob} {f₁ f₂ f₃ : hom x y} {g₁ g₂ g₃ : hom y z}
            → {s : rel f₁ f₂} {t : rel f₂ f₃} {u : rel g₁ g₂} {v : rel g₂ g₃}
            → {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
            → {f₁ᴰ : hom[ f₁ ] xᴰ yᴰ}
            → {f₂ᴰ : hom[ f₂ ] xᴰ yᴰ}
            → {f₃ᴰ : hom[ f₃ ] xᴰ yᴰ}
            → {g₁ᴰ : hom[ g₁ ] yᴰ zᴰ}
            → {g₂ᴰ : hom[ g₂ ] yᴰ zᴰ}
            → {g₃ᴰ : hom[ g₃ ] yᴰ zᴰ}
            → (sᴰ : rel[ s ] f₁ᴰ f₂ᴰ)
            → (tᴰ : rel[ t ] f₂ᴰ f₃ᴰ)
            → (uᴰ : rel[ u ] g₁ᴰ g₂ᴰ)
            → (vᴰ : rel[ v ] g₂ᴰ g₃ᴰ)
            → PathP (λ i → rel[ comp-rel-trans s t u v i ] (f₁ᴰ ∙₁ᴰ g₁ᴰ) (f₃ᴰ ∙₁ᴰ g₃ᴰ))
              ((sᴰ ∙ᵥᴰ tᴰ) ∙ₕᴰ (uᴰ ∙ᵥᴰ vᴰ))
              ((sᴰ ∙ₕᴰ uᴰ) ∙ᵥᴰ (tᴰ ∙ₕᴰ vᴰ))

        field
          comp-hom-assocᴰ : {x y z w : ob} {f : hom x y} {g : hom y z} {h : hom z w}
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
        field
          comp-rel-assocᴰ : {x y z w : ob} {f₁ f₂ : hom x y} {g₁ g₂ : hom y z} {k₁ k₂ : hom z w}
            → {s : rel f₁ f₂} {t : rel g₁ g₂} {u : rel k₁ k₂}
            → {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]} {wᴰ : ob[ w ]}
            → {f₁ᴰ : hom[ f₁ ] xᴰ yᴰ}
            → {f₂ᴰ : hom[ f₂ ] xᴰ yᴰ}
            → {g₁ᴰ : hom[ g₁ ] yᴰ zᴰ}
            → {g₂ᴰ : hom[ g₂ ] yᴰ zᴰ}
            → {k₁ᴰ : hom[ k₁ ] zᴰ wᴰ}
            → {k₂ᴰ : hom[ k₂ ] zᴰ wᴰ}
            → (sᴰ : rel[ s ] f₁ᴰ f₂ᴰ)
            → (tᴰ : rel[ t ] g₁ᴰ g₂ᴰ)
            → (uᴰ : rel[ u ] k₁ᴰ k₂ᴰ)
            → PathP (λ i → rel[ comp-rel-assoc s t u i ] (comp-hom-assocᴰ f₁ᴰ g₁ᴰ k₁ᴰ i) (comp-hom-assocᴰ f₂ᴰ g₂ᴰ k₂ᴰ i))
              ((sᴰ ∙ₕᴰ tᴰ) ∙ₕᴰ uᴰ)
              (sᴰ ∙ₕᴰ (tᴰ ∙ₕᴰ uᴰ))

          comp-rel-unit-leftᴰ : {x y : ob} {f g : hom x y} {s : rel f g}
            → {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
            → {fᴰ : hom[ f ] xᴰ yᴰ}
            → {gᴰ : hom[ g ] xᴰ yᴰ}
            → (sᴰ : rel[ s ] fᴰ gᴰ)
            → PathP (λ i → rel[ comp-rel-unit-left s i ] (comp-hom-unit-leftᴰ fᴰ i) (comp-hom-unit-leftᴰ gᴰ i))
              (id-relᴰ (id-homᴰ xᴰ) ∙ₕᴰ sᴰ)
              sᴰ

          comp-rel-unit-rightᴰ : {x y : ob} {f g : hom x y} {r : rel f g}
            → {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
            → {fᴰ : hom[ f ] xᴰ yᴰ}
            → {gᴰ : hom[ g ] xᴰ yᴰ}
            → (rᴰ : rel[ r ] fᴰ gᴰ)
            → PathP (λ i → rel[ comp-rel-unit-right r i ] (comp-hom-unit-rightᴰ fᴰ i) (comp-hom-unit-rightᴰ gᴰ i))
              (rᴰ ∙ₕᴰ id-relᴰ (id-homᴰ yᴰ))
              rᴰ

  record TwoCategoryᴰ : Type (ℓ-max ℓC (ℓ-suc (ℓMax (ℓoᴰ , ℓhᴰ , ℓrᴰ)))) where
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
      two-category-structureᴰ : TwoCategoryStrᴰ ob[_] hom[_] rel[_]
      is-two-categoryᴰ : IsTwoCategoryᴰ ob[_] hom[_] rel[_] two-category-structureᴰ

    open TwoCategoryStrᴰ two-category-structureᴰ public
    open IsTwoCategoryᴰ is-two-categoryᴰ public


module TotalTwoCategory
  {ℓo ℓh ℓr} (C : TwoCategory ℓo ℓh ℓr)
  {ℓoᴰ ℓhᴰ ℓrᴰ : Level} (Cᴰ : TwoCategoryᴰ C ℓoᴰ ℓhᴰ ℓrᴰ)
  where

  private
    open module C = TwoCategory C
    open module Cᴰ = TwoCategoryᴰ Cᴰ

    ∫₀ : Type _
    ∫₀ = Σ ob ob[_]

    ∫₁ : (x y : ∫₀) → Type _
    ∫₁ (x , xᴰ) (y , yᴰ) = Σ[ f ∈ hom x y ] hom[ f ] xᴰ yᴰ

    ∫₂ : {x y : ∫₀} (f g : ∫₁ x y) → Type _
    ∫₂ (f , fᴰ) (g , gᴰ) = Σ[ r ∈ rel f g ] rel[ r ] fᴰ gᴰ

    ∫₁≡ : {x y : ∫₀} {f g : ∫₁ x y}
      → (p : f .fst ≡ g .fst)
      → (pᴰ : PathP (λ i → hom[ p i ] (x .snd) (y .snd)) (f .snd) (g .snd))
      → f ≡ g
    ∫₁≡ p pᴰ i .fst = p i
    ∫₁≡ p pᴰ i .snd = pᴰ i

    ∫₂≡ : {x y : ∫₀} {f g : ∫₁ x y} {r s : ∫₂ f g}
      → (p : r .fst ≡ s .fst)
      → (pᴰ : PathP (λ i → rel[ p i ] (f .snd) (g .snd)) (r .snd) (s .snd))
      → r ≡ s
    ∫₂≡ p pᴰ i .fst = p i
    ∫₂≡ p pᴰ i .snd = pᴰ i

  ∫-two-category-structure : TwoCategoryStr ∫₀ ∫₁ ∫₂
  ∫-two-category-structure .TwoCategoryStr.id-hom (x , xᴰ) = id-hom x , id-homᴰ xᴰ
  ∫-two-category-structure .TwoCategoryStr.comp-hom (f , fᴰ) (g , gᴰ) = (f ∙₁ g) , fᴰ ∙₁ᴰ gᴰ
  ∫-two-category-structure .TwoCategoryStr.id-rel (f , fᴰ) = id-rel f , id-relᴰ fᴰ
  ∫-two-category-structure .TwoCategoryStr.trans (r , rᴰ) (s , sᴰ) = r ∙ᵥ s , rᴰ ∙ᵥᴰ sᴰ
  ∫-two-category-structure .TwoCategoryStr.comp-rel (r , rᴰ) (s , sᴰ) = r ∙ₕ s , rᴰ ∙ₕᴰ sᴰ

  ∫-is-two-cat : IsTwoCategory ∫₀ ∫₁ ∫₂ ∫-two-category-structure
  ∫-is-two-cat .IsTwoCategory.is-set-rel (f , fᴰ) (g , gᴰ) = isSetΣ (is-set-rel f g) λ r → (is-set-relᴰ fᴰ gᴰ)
  ∫-is-two-cat .IsTwoCategory.trans-assoc (r , rᴰ) (s , sᴰ) (t , tᴰ) i .fst = trans-assoc r s t i
  ∫-is-two-cat .IsTwoCategory.trans-assoc (r , rᴰ) (s , sᴰ) (t , tᴰ) i .snd = trans-assocᴰ rᴰ sᴰ tᴰ i
  ∫-is-two-cat .IsTwoCategory.trans-unit-left (r , rᴰ) i .fst = trans-unit-left r i
  ∫-is-two-cat .IsTwoCategory.trans-unit-left (r , rᴰ) i .snd = trans-unit-leftᴰ rᴰ i
  ∫-is-two-cat .IsTwoCategory.trans-unit-right (r , rᴰ) i .fst = trans-unit-right r i
  ∫-is-two-cat .IsTwoCategory.trans-unit-right (r , rᴰ) i .snd = trans-unit-rightᴰ rᴰ i
  ∫-is-two-cat .IsTwoCategory.comp-rel-id (f , fᴰ) (g , gᴰ) i .fst = comp-rel-id f g i
  ∫-is-two-cat .IsTwoCategory.comp-rel-id (f , fᴰ) (g , gᴰ) i .snd = comp-rel-idᴰ fᴰ gᴰ i
  ∫-is-two-cat .IsTwoCategory.comp-rel-trans (s , sᴰ) (t , tᴰ) (u , uᴰ) (v , vᴰ) i .fst = comp-rel-trans s t u v i
  ∫-is-two-cat .IsTwoCategory.comp-rel-trans (s , sᴰ) (t , tᴰ) (u , uᴰ) (v , vᴰ) i .snd = comp-rel-transᴰ sᴰ tᴰ uᴰ vᴰ i
  ∫-is-two-cat .IsTwoCategory.comp-hom-assoc (f , fᴰ) (g , gᴰ) (h , hᴰ) = ∫₁≡ (comp-hom-assoc f g h) (comp-hom-assocᴰ fᴰ gᴰ hᴰ)
  ∫-is-two-cat .IsTwoCategory.comp-hom-unit-left (g , gᴰ) = ∫₁≡ (comp-hom-unit-left g) (comp-hom-unit-leftᴰ gᴰ)
  ∫-is-two-cat .IsTwoCategory.comp-hom-unit-right (f , fᴰ) = ∫₁≡ (comp-hom-unit-right f) (comp-hom-unit-rightᴰ fᴰ)
  ∫-is-two-cat .IsTwoCategory.comp-rel-assoc (s , sᴰ) (t , tᴰ) (u , uᴰ) i .fst = comp-rel-assoc s t u i
  ∫-is-two-cat .IsTwoCategory.comp-rel-assoc (s , sᴰ) (t , tᴰ) (u , uᴰ) i .snd = comp-rel-assocᴰ sᴰ tᴰ uᴰ i
  ∫-is-two-cat .IsTwoCategory.comp-rel-unit-left (s , sᴰ) i .fst = comp-rel-unit-left s i
  ∫-is-two-cat .IsTwoCategory.comp-rel-unit-left (s , sᴰ) i .snd = comp-rel-unit-leftᴰ sᴰ i
  ∫-is-two-cat .IsTwoCategory.comp-rel-unit-right (r , rᴰ) i .fst = comp-rel-unit-right r i
  ∫-is-two-cat .IsTwoCategory.comp-rel-unit-right (r , rᴰ) i .snd = comp-rel-unit-rightᴰ rᴰ i

  ∫ : TwoCategory (ℓ-max ℓo ℓoᴰ) (ℓ-max ℓh ℓhᴰ) (ℓ-max ℓr ℓrᴰ)
  ∫ .TwoCategory.ob = ∫₀
  ∫ .TwoCategory.hom = ∫₁
  ∫ .TwoCategory.rel = ∫₂
  ∫ .TwoCategory.two-category-structure = ∫-two-category-structure
  ∫ .TwoCategory.is-two-category = ∫-is-two-cat
