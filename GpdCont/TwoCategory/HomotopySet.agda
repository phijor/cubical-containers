module GpdCont.TwoCategory.HomotopySet where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LocallyThin

open import Cubical.Foundations.HLevels
open import Cubical.Categories.Instances.Sets using (SET)

module _ (ℓ : Level) where
  hSetCat : TwoCategory (ℓ-suc ℓ) ℓ ℓ
  hSetCat = LocallyThin (SET ℓ)
