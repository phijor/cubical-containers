module GpdCont.TwoCategory.Subcategory where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LaxFunctor

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

  Forget : LaxFunctor Subcategory C
  Forget .LaxFunctor.F-ob = fst
  Forget .LaxFunctor.F-hom = id _
  Forget .LaxFunctor.F-rel = id _
  Forget .LaxFunctor.F-rel-id = refl
  Forget .LaxFunctor.F-rel-trans r s = refl
  Forget .LaxFunctor.F-trans-lax f g = id-rel (f ∙₁ g)
  Forget .LaxFunctor.F-trans-lax-natural r s = trans-unit-right (r ∙ₕ s) ∙ (sym (trans-unit-left (r ∙ₕ s)))
  Forget .LaxFunctor.F-id-lax (x , _) = id-rel (id-hom x)
  Forget .LaxFunctor.F-assoc f g h = doubleCompPathP (λ i j → C.rel (comp-hom-assoc f g h j) (comp-hom-assoc f g h j)) left (comp-rel-assoc (id-rel f) (id-rel g) (id-rel h)) {! !}
    where
      left : (id-rel f ∙ₕ id-rel g) ∙ₕ id-rel h ≡ (id-rel (f ∙₁ g) ∙ₕ id-rel h) ∙ᵥ (id-rel ((f ∙₁ g) ∙₁ h))
      left = {! !}
  Forget .LaxFunctor.F-unit-left f = doubleCompPathP (λ i j → C.rel (comp-hom-unit-left f j) (comp-hom-unit-left f j)) {! !} (comp-rel-unit-left (id-rel f)) {! !}
  Forget .LaxFunctor.F-unit-right = {! !}
