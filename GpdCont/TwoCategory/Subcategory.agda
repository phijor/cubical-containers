module GpdCont.TwoCategory.Subcategory where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

open import Cubical.Foundations.HLevels

module _ {ℓo ℓh ℓr ℓ} (C : TwoCategory ℓo ℓh ℓr) (P : C .TwoCategory.ob → hProp ℓ) where
  private
    open module C = TwoCategory C

  Subcategory : TwoCategory (ℓ-max ℓo ℓ) ℓh ℓr
  Subcategory .TwoCategory.ob = Σ[ x ∈ ob ] ⟨ P x ⟩
  Subcategory .TwoCategory.hom (x , _) (y , _) = hom x y
  Subcategory .TwoCategory.rel = rel
  Subcategory .TwoCategory.two-category-structure = two-cat-str where
    two-cat-str : TwoCategoryStr _ _ _
    two-cat-str .TwoCategoryStr.id-hom (x , _) = id-hom x
    two-cat-str .TwoCategoryStr.comp-hom = comp-hom
    two-cat-str .TwoCategoryStr.id-rel = id-rel
    two-cat-str .TwoCategoryStr.trans = trans
    two-cat-str .TwoCategoryStr.comp-rel = comp-rel
  Subcategory .TwoCategory.is-two-category = record { IsTwoCategory (C.is-two-category) }
