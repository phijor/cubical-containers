module GpdCont.TwoCategory.TwoDiscrete where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.WildCat.Base using (WildCat ; _[_,_])

module _ {ℓo ℓh} (C : WildCat ℓo ℓh) (isGroupoidHom : (x y : WildCat.ob C) → isGroupoid (C [ x , y ])) where
  private
    module C = WildCat C

    variable
      x y z w : C.ob
      f f₁ f₂ f₃ : C.Hom[ x , y ]
      g g₁ g₂ g₃ : C.Hom[ y , z ]
      k k₁ k₂ k₃ : C.Hom[ z , w ]

    _∙ₕ_ :
        f₁ ≡ f₂
      → g₁ ≡ g₂
      → f₁ C.⋆ g₁ ≡ f₂ C.⋆ g₂
    _∙ₕ_ p q = cong₂ C._⋆_ p q

    ∙ₕ-interchange :
      ∀ (f₁≡f₂ : f₁ ≡ f₂)
      → (f₂≡f₃ : f₂ ≡ f₃)
      → (g₁≡g₂ : g₁ ≡ g₂)
      → (g₂≡g₃ : g₂ ≡ g₃)
      → (f₁≡f₂ ∙ f₂≡f₃) ∙ₕ (g₁≡g₂ ∙ g₂≡g₃) ≡ (f₁≡f₂ ∙ₕ g₁≡g₂) ∙ (f₂≡f₃ ∙ₕ g₂≡g₃)
    ∙ₕ-interchange = cong₂-∙ C._⋆_

    ∙ₕ-assoc :
      ∀ (f₁≡f₂ : f₁ ≡ f₂)
      → (g₁≡g₂ : g₁ ≡ g₂)
      → (k₁≡k₂ : k₁ ≡ k₂)
      → PathP (λ j → C.⋆Assoc f₁ g₁ k₁ j ≡ C.⋆Assoc f₂ g₂ k₂ j) ((f₁≡f₂ ∙ₕ g₁≡g₂) ∙ₕ k₁≡k₂) (f₁≡f₂ ∙ₕ (g₁≡g₂ ∙ₕ k₁≡k₂))
    ∙ₕ-assoc {f₁} {f₂} {g₁} {g₂} {k₁} {k₂} f₁≡f₂ g₁≡g₂ k₁≡k₂ = assoc' where
      assoc' : Square ((f₁≡f₂ ∙ₕ g₁≡g₂) ∙ₕ k₁≡k₂) (f₁≡f₂ ∙ₕ (g₁≡g₂ ∙ₕ k₁≡k₂)) (C.⋆Assoc f₁ g₁ k₁) (C.⋆Assoc f₂ g₂ k₂)
      assoc' j i = C.⋆Assoc (f₁≡f₂ i) (g₁≡g₂ i) (k₁≡k₂ i) j

    ∙ₕ-lUnit : ∀ (p : f ≡ g) → PathP (λ j → C.⋆IdL f j ≡ C.⋆IdL g j) (refl ∙ₕ p) p
    ∙ₕ-lUnit p j i = C.⋆IdL (p i) j

    ∙ₕ-rUnit : ∀ (p : f ≡ g) → PathP (λ j → C.⋆IdR f j ≡ C.⋆IdR g j) (p ∙ₕ refl) p
    ∙ₕ-rUnit p j i = C.⋆IdR (p i) j

  twoDiscreteStr : TwoCategoryStr C.ob C.Hom[_,_] _≡_
  twoDiscreteStr .TwoCategoryStr.id-hom x = C.id {x}
  twoDiscreteStr .TwoCategoryStr.comp-hom = C._⋆_
  twoDiscreteStr .TwoCategoryStr.id-rel f = refl′ f
  twoDiscreteStr .TwoCategoryStr.trans = _∙_
  twoDiscreteStr .TwoCategoryStr.comp-rel = _∙ₕ_

  isTwoCategoryTwoDiscreteStr : IsTwoCategory _ _ _ twoDiscreteStr
  isTwoCategoryTwoDiscreteStr .IsTwoCategory.is-set-rel {x} {y} = isGroupoidHom x y
  isTwoCategoryTwoDiscreteStr .IsTwoCategory.trans-assoc f≡g g≡h h≡k = sym $ GL.assoc f≡g g≡h h≡k
  isTwoCategoryTwoDiscreteStr .IsTwoCategory.trans-unit-left f≡g = sym $ GL.lUnit f≡g
  isTwoCategoryTwoDiscreteStr .IsTwoCategory.trans-unit-right f≡g = sym $ GL.rUnit f≡g
  isTwoCategoryTwoDiscreteStr .IsTwoCategory.comp-rel-id f g = λ i j → f C.⋆ g
  isTwoCategoryTwoDiscreteStr .IsTwoCategory.comp-rel-trans  = ∙ₕ-interchange
  isTwoCategoryTwoDiscreteStr .IsTwoCategory.comp-hom-assoc = C.⋆Assoc
  isTwoCategoryTwoDiscreteStr .IsTwoCategory.comp-hom-unit-left = C.⋆IdL
  isTwoCategoryTwoDiscreteStr .IsTwoCategory.comp-hom-unit-right = C.⋆IdR
  isTwoCategoryTwoDiscreteStr .IsTwoCategory.comp-rel-assoc = ∙ₕ-assoc
  isTwoCategoryTwoDiscreteStr .IsTwoCategory.comp-rel-unit-left = ∙ₕ-lUnit
  isTwoCategoryTwoDiscreteStr .IsTwoCategory.comp-rel-unit-right = ∙ₕ-rUnit

  TwoDiscrete : TwoCategory ℓo ℓh ℓh
  TwoDiscrete .TwoCategory.ob = C.ob
  TwoDiscrete .TwoCategory.hom = C.Hom[_,_]
  TwoDiscrete .TwoCategory.rel = _≡_
  TwoDiscrete .TwoCategory.two-category-structure = twoDiscreteStr
  TwoDiscrete .TwoCategory.is-two-category = isTwoCategoryTwoDiscreteStr
