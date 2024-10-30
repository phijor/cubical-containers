module GpdCont.TwoCategory.LocallyThin where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.TwoDiscrete

open import Cubical.Foundations.HLevels using (isSet→isGroupoid)
open import Cubical.Categories.Category.Base
open import Cubical.WildCat.Base

module _ {ℓo ℓh} (C : Category ℓo ℓh) where
  private
    module C = Category C

    C-wild : WildCat ℓo ℓh
    C-wild = record { C }

  LocallyThin : TwoCategory ℓo ℓh ℓh
  LocallyThin = TwoDiscrete C-wild λ x y → isSet→isGroupoid C.isSetHom
