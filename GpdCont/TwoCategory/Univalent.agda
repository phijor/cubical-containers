module GpdCont.TwoCategory.Univalent where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LocalCategory

open import Cubical.Categories.Category.Base using (isUnivalent)

-- A 2-category is locally univalent if all of its hom-categories are univalent.
module _ {ℓo ℓh ℓr} (C : TwoCategory ℓo ℓh ℓr) where
  isLocallyUnivalent : Type _
  isLocallyUnivalent = ∀ x y → isUnivalent (LocalCategory C x y)
