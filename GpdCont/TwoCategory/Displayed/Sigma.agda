module GpdCont.TwoCategory.Displayed.Sigma where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Displayed.Base

open TotalTwoCategory using (∫)

module _ {ℓo ℓh ℓr ℓo′ ℓh′ ℓr′ ℓo″ ℓh″ ℓr″}
  {C : TwoCategory ℓo ℓh ℓr}
  (D : TwoCategoryᴰ C ℓo′ ℓh′ ℓr′)
  (E : TwoCategoryᴰ (∫ C D) ℓo″ ℓh″ ℓr″)
  where
    private
      module C = TwoCategory C
      module D = TwoCategoryᴰ D
      module E = TwoCategoryᴰ E

    Σᴰ₀ : C.ob → Type _
    Σᴰ₀ x = Σ[ xᴰ ∈ D.ob[ x ] ] E.ob[ x , xᴰ ]
    
    Σᴰ₁ : ∀ {x y} → C.hom x y → Σᴰ₀ x → Σᴰ₀ y → Type _
    Σᴰ₁ f (xᴰ , xᴱ) (yᴰ , yᴱ) = Σ[ fᴰ ∈ D.hom[ f ] xᴰ yᴰ ] E.hom[ f , fᴰ ] xᴱ yᴱ

    Σᴰ₂ : ∀ {x y} {f g : C.hom x y} {xᴰ : Σᴰ₀ x} {yᴰ : Σᴰ₀ y}
      → C.rel f g
      → Σᴰ₁ f xᴰ yᴰ
      → Σᴰ₁ g xᴰ yᴰ
      → Type _
    Σᴰ₂ r (fᴰ , fᴱ) (gᴰ , gᴱ) = Σ[ rᴰ ∈ D.rel[ r ] fᴰ gᴰ ] E.rel[ r , rᴰ ] fᴱ gᴱ

    Σᴰ : TwoCategoryᴰ C (ℓ-max ℓo′ ℓo″) (ℓ-max ℓh′ ℓh″) (ℓ-max ℓr′ ℓr″)
    Σᴰ .TwoCategoryᴰ.ob[_] = Σᴰ₀
    Σᴰ .TwoCategoryᴰ.hom[_] = Σᴰ₁
    Σᴰ .TwoCategoryᴰ.rel[_] = Σᴰ₂
    Σᴰ .TwoCategoryᴰ.two-category-structureᴰ = {! !}
    Σᴰ .TwoCategoryᴰ.is-two-categoryᴰ = {! !}
