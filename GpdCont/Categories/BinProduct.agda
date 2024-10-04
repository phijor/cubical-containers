module GpdCont.Categories.BinProduct where

open import GpdCont.Prelude hiding (_⋆_)

open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct renaming (_×C_ to _×Cat_)
open import Cubical.Categories.Constructions.TotalCategory.Base using (∫C)
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.StructureOver.Base

private
  variable
    ℓo ℓh ℓo′ ℓh′ : Level

  UP-at : ∀ {C : Category ℓo ℓh} {x y} (x×y : BinProduct C x y) {z}
    → (f₁ : C [ z , x ])
    → (f₂ : C [ z , y ])
    → Type _
  UP-at {C} x×y {z} f₁ f₂ = ∃![ f ∈ C [ z , binProdOb ] ] (f ⋆ binProdPr₁ ≡ f₁) × (f ⋆ binProdPr₂ ≡ f₂) where
    open Category C
    open BinProduct x×y

module _ (C : Category ℓo ℓh) (D : Category ℓo′ ℓh′)
  (bpC : BinProducts C)
  (bpD : BinProducts D)
  where
  private
    module C = Notation C bpC
    module D = Notation D bpD

  ProductCategoryBinProducts' : BinProducts' (C ×Cat D)
  ProductCategoryBinProducts' = {! !}

  ProductCategoryBinProducts : BinProducts (C ×Cat D)
  ProductCategoryBinProducts (c₀ , d₀) (c₁ , d₁) = prod where
    c₀×c₁ = bpC c₀ c₁
    d₀×d₁ = bpD d₀ d₁

    module c₀×c₁ = BinProduct c₀×c₁
    module d₀×d₁ = BinProduct d₀×d₁

    prod : BinProduct _ _ _
    prod .BinProduct.binProdOb = c₀ C.× c₁ , d₀ D.× d₁
    prod .BinProduct.binProdPr₁ = C.π₁ , D.π₁
    prod .BinProduct.binProdPr₂ = C.π₂ , D.π₂
    prod .BinProduct.univProp (f₁ , g₁) (f₂ , g₂) = goal where
      f₁×f₂ = c₀×c₁.univProp f₁ f₂
      g₁×g₂ = d₀×d₁.univProp g₁ g₂

      goal : isContr _
      goal .fst = (f₁×f₂ .fst .fst , g₁×g₂ .fst .fst) , ≡-× (f₁×f₂ .fst .snd .fst) (g₁×g₂ .fst .snd .fst)  , ≡-× (f₁×f₂ .fst .snd .snd) (g₁×g₂ .fst .snd .snd)
      goal .snd y i = (f₁×f₂ .snd {!y !} i .fst , {! !}) , {! !}

module TotalCategoryBinProducts
  (C : Category ℓo ℓh) (bp : BinProducts C)
  (D : Categoryᴰ C ℓo′ ℓh′) (bpᴰ : ?)
  where

  ∫BinProducts : BinProducts (∫C {C = C} D)
  ∫BinProducts (x , xᴰ) (y , yᵈ) = {! !}
