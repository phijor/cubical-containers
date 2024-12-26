module GpdCont.TwoCategory.Subcategory where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.StrictFunctor using (StrictFunctor)

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

  ForgetLax : LaxFunctor Subcategory C
  ForgetLax .LaxFunctor.F-ob = fst
  ForgetLax .LaxFunctor.F-hom = id _
  ForgetLax .LaxFunctor.F-rel = id _
  ForgetLax .LaxFunctor.F-rel-id = refl
  ForgetLax .LaxFunctor.F-rel-trans r s = refl
  ForgetLax .LaxFunctor.F-trans-lax f g = id-rel (f ∙₁ g)
  ForgetLax .LaxFunctor.F-trans-lax-natural r s = trans-unit-right (r ∙ₕ s) ∙ (sym (trans-unit-left (r ∙ₕ s)))
  ForgetLax .LaxFunctor.F-id-lax (x , _) = id-rel (id-hom x)
  ForgetLax .LaxFunctor.F-assoc f g h = doubleCompPathP (λ i j → C.rel (comp-hom-assoc f g h j) (comp-hom-assoc f g h j)) left (comp-rel-assoc (id-rel f) (id-rel g) (id-rel h)) {! !}
    where
      left : (id-rel f ∙ₕ id-rel g) ∙ₕ id-rel h ≡ (id-rel (f ∙₁ g) ∙ₕ id-rel h) ∙ᵥ (id-rel ((f ∙₁ g) ∙₁ h))
      left = {! !}
  ForgetLax .LaxFunctor.F-unit-left f = doubleCompPathP (λ i j → C.rel (comp-hom-unit-left f j) (comp-hom-unit-left f j)) {! !} (comp-rel-unit-left (id-rel f)) {! !}
  ForgetLax .LaxFunctor.F-unit-right = {! !}

  Forget : StrictFunctor Subcategory C
  Forget .StrictFunctor.F-ob = fst
  Forget .StrictFunctor.F-hom = id _
  Forget .StrictFunctor.F-rel = id _
  Forget .StrictFunctor.F-rel-id {f} = refl′ (id-rel f)
  Forget .StrictFunctor.F-rel-trans r s = refl′ (r ∙ᵥ s)
  Forget .StrictFunctor.F-hom-comp f g = refl′ (f ∙₁ g)
  Forget .StrictFunctor.F-hom-id (x , _) = refl′ (id-hom x)
  Forget .StrictFunctor.F-assoc-filler-left f g h .fst = refl′ ((f ∙₁ g) ∙₁ h)
  Forget .StrictFunctor.F-assoc-filler-left f g h .snd = refl
  Forget .StrictFunctor.F-assoc-filler-right f g h .fst = refl′ (f ∙₁ (g ∙₁ h))
  Forget .StrictFunctor.F-assoc-filler-right f g h .snd = refl
  Forget .StrictFunctor.F-assoc f g h = λ i j → comp-hom-assoc f g h i
  Forget .StrictFunctor.F-unit-left-filler {x = x , _} f .fst = refl′ (id-hom x ∙₁ f)
  Forget .StrictFunctor.F-unit-left-filler f .snd = refl
  Forget .StrictFunctor.F-unit-left f = λ i j → comp-hom-unit-left f i
  Forget .StrictFunctor.F-unit-right-filler {y = y , _} f .fst = refl′ (f ∙₁ id-hom y)
  Forget .StrictFunctor.F-unit-right-filler f .snd = refl
  Forget .StrictFunctor.F-unit-right f = λ i j → comp-hom-unit-right f i
