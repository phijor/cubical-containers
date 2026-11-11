module GpdCont.TwoCategory.LocallyDiscrete where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Univalent
open import GpdCont.TwoCategory.LocalCategory

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

  locallyDiscreteStr : TwoCategoryStr C.ob C.Hom[_,_] _≡_
  locallyDiscreteStr .TwoCategoryStr.id-hom x = C.id {x}
  locallyDiscreteStr .TwoCategoryStr.comp-hom = C._⋆_
  locallyDiscreteStr .TwoCategoryStr.id-rel f = refl′ f
  locallyDiscreteStr .TwoCategoryStr.trans = _∙_
  locallyDiscreteStr .TwoCategoryStr.comp-rel = _∙ₕ_

  isTwoCategoryLocallyDiscreteStr : IsTwoCategory _ _ _ locallyDiscreteStr
  isTwoCategoryLocallyDiscreteStr .IsTwoCategory.is-set-rel {x} {y} = isGroupoidHom x y
  isTwoCategoryLocallyDiscreteStr .IsTwoCategory.trans-assoc f≡g g≡h h≡k = sym $ GL.assoc f≡g g≡h h≡k
  isTwoCategoryLocallyDiscreteStr .IsTwoCategory.trans-unit-left f≡g = sym $ GL.lUnit f≡g
  isTwoCategoryLocallyDiscreteStr .IsTwoCategory.trans-unit-right f≡g = sym $ GL.rUnit f≡g
  isTwoCategoryLocallyDiscreteStr .IsTwoCategory.comp-rel-id f g = λ i j → f C.⋆ g
  isTwoCategoryLocallyDiscreteStr .IsTwoCategory.comp-rel-trans  = ∙ₕ-interchange
  isTwoCategoryLocallyDiscreteStr .IsTwoCategory.comp-hom-assoc = C.⋆Assoc
  isTwoCategoryLocallyDiscreteStr .IsTwoCategory.comp-hom-unit-left = C.⋆IdL
  isTwoCategoryLocallyDiscreteStr .IsTwoCategory.comp-hom-unit-right = C.⋆IdR
  isTwoCategoryLocallyDiscreteStr .IsTwoCategory.comp-rel-assoc = ∙ₕ-assoc
  isTwoCategoryLocallyDiscreteStr .IsTwoCategory.comp-rel-unit-left = ∙ₕ-lUnit
  isTwoCategoryLocallyDiscreteStr .IsTwoCategory.comp-rel-unit-right = ∙ₕ-rUnit

  LocallyDiscrete : TwoCategory ℓo ℓh ℓh
  LocallyDiscrete .TwoCategory.ob = C.ob
  LocallyDiscrete .TwoCategory.hom = C.Hom[_,_]
  LocallyDiscrete .TwoCategory.rel = _≡_
  LocallyDiscrete .TwoCategory.two-category-structure = locallyDiscreteStr
  LocallyDiscrete .TwoCategory.is-two-category = isTwoCategoryLocallyDiscreteStr

  isLocallyUnivalentLocallyDiscrete : isLocallyUnivalent LocallyDiscrete
  isLocallyUnivalentLocallyDiscrete x y = is-univ where
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Foundations.Equiv
    open import Cubical.Data.Sigma
    open import Cubical.Categories.Category.Base

    x≡y : Category _ _
    x≡y = LocalCategory LocallyDiscrete x y

    pathToIso′ : ∀ {f₁ f₂} (p : f₁ ≡ f₂) → CatIso x≡y f₁ f₂
    pathToIso′ p = p , isiso (sym p) (GL.lCancel p) (GL.rCancel p)

    coh : ∀ f₁ f₂ → pathToIso′ {f₁} {f₂} ≡ pathToIso
    coh f₁ f₂ = funExt (J (λ f₂ (p : f₁ ≡ f₂) → pathToIso′ p ≡ pathToIso p) (sym pathToIso-refl))

    isEquivPathToIso′ : ∀ f₁ f₂ → isEquiv (pathToIso′ {f₁} {f₂})
    isEquivPathToIso′ f₁ f₂ = isoToIsEquiv (iso pathToIso′ fst (λ { (p , is-iso) → Σ≡Prop (λ _ → isPropIsIso _) refl }) λ _ → refl)

    is-univ : isUnivalent _
    is-univ .isUnivalent.univ f₁ f₂ = subst isEquiv (coh f₁ f₂) (isEquivPathToIso′ f₁ f₂)
