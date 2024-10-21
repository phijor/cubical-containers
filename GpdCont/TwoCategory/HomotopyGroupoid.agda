module GpdCont.TwoCategory.HomotopyGroupoid where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Isomorphism

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

private
  variable
    ℓ ℓ' : Level
    X Y Z : Type ℓ

  isGroupoid→ : isGroupoid Y → isGroupoid (X → Y)
  isGroupoid→ = isGroupoidΠ ∘ const

  _→Gpd_ : (X Y : hGroupoid ℓ) → hGroupoid ℓ
  X →Gpd Y = (⟨ X ⟩ → ⟨ Y ⟩) , isGroupoid→ (str Y)

  _∙htpy_ : ∀ {f₁ f₂ : X → Y} {g₁ g₂ : Y → Z}
    → (p : f₁ ≡ f₂)
    → (q : g₁ ≡ g₂)
    → (f₁ ⋆ g₁ ≡ f₂ ⋆ g₂)
  _∙htpy_ p q = cong₂ _⋆_ p q
  
module _ (ℓ : Level) where
  hGpdCat : TwoCategory (ℓ-suc ℓ) ℓ ℓ
  hGpdCat .TwoCategory.ob = hGroupoid ℓ
  hGpdCat .TwoCategory.hom X Y = ⟨ X ⟩ → ⟨ Y ⟩
  hGpdCat .TwoCategory.rel f g = f ≡ g
  hGpdCat .TwoCategory.two-category-structure = cat-str where
    cat-str : TwoCategoryStr _ _ _
    cat-str .TwoCategoryStr.id-hom X = id ⟨ X ⟩
    cat-str .TwoCategoryStr.comp-hom = _⋆_
    cat-str .TwoCategoryStr.id-rel f = refl
    cat-str .TwoCategoryStr.trans p q = p ∙ q
    cat-str .TwoCategoryStr.comp-rel = _∙htpy_
  hGpdCat .TwoCategory.is-two-category = is-cat where
    is-cat : IsTwoCategory _ _ _ _
    is-cat .IsTwoCategory.is-set-rel {y = Y} = isGroupoid→ (str Y)
    is-cat .IsTwoCategory.trans-assoc r s t = sym (assoc r s t)
    is-cat .IsTwoCategory.trans-unit-left s = sym (lUnit s)
    is-cat .IsTwoCategory.trans-unit-right r = sym (rUnit r)
    is-cat .IsTwoCategory.comp-rel-id f g = refl
    is-cat .IsTwoCategory.comp-rel-trans s t u v = cong₂-∙ _⋆_ s t u v
    is-cat .IsTwoCategory.comp-hom-assoc f g h = refl
    is-cat .IsTwoCategory.comp-hom-unit-left g = refl
    is-cat .IsTwoCategory.comp-hom-unit-right f = refl
    is-cat .IsTwoCategory.comp-rel-assoc s t u = refl
    is-cat .IsTwoCategory.comp-rel-unit-left s = refl
    is-cat .IsTwoCategory.comp-rel-unit-right r = refl

  open LocalIso using (isLocallyGroupoidal ; isLocalInverse)

  isLocallyGroupoidalHGpdCat : isLocallyGroupoidal hGpdCat
  isLocallyGroupoidalHGpdCat p .fst = sym p
  isLocallyGroupoidalHGpdCat p .snd .isLocalInverse.dom-id = rCancel p
  isLocallyGroupoidalHGpdCat p .snd .isLocalInverse.codom-id = lCancel p
