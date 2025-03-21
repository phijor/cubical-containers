open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

module GpdCont.TwoCategory.Product {ℓIx ℓo ℓh ℓr} (Ix : Type ℓIx) (C : TwoCategory ℓo ℓh ℓr) where

open import Cubical.Foundations.HLevels

private
  module C = TwoCategory C
  postulate
    trustme : ∀ {ℓ} {A : Type ℓ} → A

Δ : TwoCategory (ℓ-max ℓIx ℓo) (ℓ-max ℓIx ℓh) (ℓ-max ℓIx ℓr)
Δ .TwoCategory.ob = Ix → C.ob
Δ .TwoCategory.hom x y = (ix : Ix) → C.hom (x ix) (y ix)
Δ .TwoCategory.rel f g = (ix : Ix) → C.rel (f ix) (g ix)
Δ .TwoCategory.two-category-structure .TwoCategoryStr.id-hom x ix = C.id-hom (x ix)
Δ .TwoCategory.two-category-structure .TwoCategoryStr.comp-hom f g ix = C.comp-hom (f ix) (g ix)
Δ .TwoCategory.two-category-structure .TwoCategoryStr.id-rel f ix = C.id-rel (f ix)
Δ .TwoCategory.two-category-structure .TwoCategoryStr.trans r s ix = C.trans (r ix) (s ix)
Δ .TwoCategory.two-category-structure .TwoCategoryStr.comp-rel r s ix = C.comp-rel (r ix) (s ix)
Δ .TwoCategory.is-two-category .IsTwoCategory.is-set-rel f g = isSetΠ λ ix → C.is-set-rel (f ix) (g ix)
Δ .TwoCategory.is-two-category .IsTwoCategory.trans-assoc = trustme
Δ .TwoCategory.is-two-category .IsTwoCategory.trans-unit-left = trustme
Δ .TwoCategory.is-two-category .IsTwoCategory.trans-unit-right = trustme
Δ .TwoCategory.is-two-category .IsTwoCategory.comp-rel-id = trustme
Δ .TwoCategory.is-two-category .IsTwoCategory.comp-rel-trans = trustme
Δ .TwoCategory.is-two-category .IsTwoCategory.comp-hom-assoc = trustme
Δ .TwoCategory.is-two-category .IsTwoCategory.comp-hom-unit-left = trustme
Δ .TwoCategory.is-two-category .IsTwoCategory.comp-hom-unit-right = trustme
Δ .TwoCategory.is-two-category .IsTwoCategory.comp-rel-assoc = trustme
Δ .TwoCategory.is-two-category .IsTwoCategory.comp-rel-unit-left = trustme
Δ .TwoCategory.is-two-category .IsTwoCategory.comp-rel-unit-right = trustme
