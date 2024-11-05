module GpdCont.TwoCategory.BinProduct where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

open import Cubical.Data.Sigma

private
  variable
    ℓo ℓh ℓr ℓo′ ℓh′ ℓr′ : Level

module _ (C : TwoCategory ℓo ℓh ℓr) (D : TwoCategory ℓo′ ℓh′ ℓr′) where
  private
    module C = TwoCategory C
    module D = TwoCategory D

  BinProduct : TwoCategory (ℓ-max ℓo ℓo′) (ℓ-max ℓh ℓh′) (ℓ-max ℓr ℓr′)
  BinProduct .TwoCategory.ob = C.ob × D.ob
  BinProduct .TwoCategory.hom (f , f′) (g , g′) = C.hom f g × D.hom f′ g′
  BinProduct .TwoCategory.rel (r , r′) (s , s′) = C.rel r s × D.rel r′ s′
  BinProduct .TwoCategory.two-category-structure = bin-prod-str where
    bin-prod-str : TwoCategoryStr _ _ _
    bin-prod-str .TwoCategoryStr.id-hom (x , x′) = C.id-hom x , D.id-hom x′
    bin-prod-str .TwoCategoryStr.comp-hom (f , f′) (g , g′) = C.comp-hom f g , D.comp-hom f′ g′
    bin-prod-str .TwoCategoryStr.id-rel (f , f′) = C.id-rel f , D.id-rel f′
    bin-prod-str .TwoCategoryStr.trans (r , r′) (s , s′) = C.trans r s , D.trans r′ s′
    bin-prod-str .TwoCategoryStr.comp-rel (r , r′) (s , s′) = C.comp-rel r s , D.comp-rel r′ s′
  BinProduct .TwoCategory.is-two-category = {! !}
