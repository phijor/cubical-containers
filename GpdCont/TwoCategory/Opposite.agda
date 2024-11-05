module GpdCont.TwoCategory.Opposite where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

open import Cubical.Foundations.Function using (flip)

private
  variable
    ℓo ℓh ℓr : Level

module _ (C : TwoCategory ℓo ℓh ℓr) where
  private
    module C = TwoCategory C

  Op : TwoCategory ℓo ℓh ℓr
  Op .TwoCategory.ob = C.ob
  Op .TwoCategory.hom = flip C.hom
  Op .TwoCategory.rel = C.rel
  Op .TwoCategory.two-category-structure = op-str where
    op-str : TwoCategoryStr C.ob _ C.rel
    op-str = record
      { C
      ; comp-hom = flip C.comp-hom
      ; comp-rel = flip C.comp-rel
      }
  Op .TwoCategory.is-two-category = record
    { C
    ; comp-rel-id = flip C.comp-rel-id
    ; comp-rel-trans = λ s t u v → C.comp-rel-trans u v s t
    ; comp-hom-assoc = λ f g h → sym $ C.comp-hom-assoc h g f
    ; comp-hom-unit-left = C.comp-hom-unit-right
    ; comp-hom-unit-right = C.comp-hom-unit-left
    ; comp-rel-assoc = λ s t u i → C.comp-rel-assoc u t s (~ i)
    ; comp-rel-unit-left = C.comp-rel-unit-right
    ; comp-rel-unit-right = C.comp-rel-unit-left
    }

_ᵒᵖ : TwoCategory ℓo ℓh ℓr → TwoCategory ℓo ℓh ℓr
_ᵒᵖ = Op
