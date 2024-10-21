module GpdCont.GroupoidContainer.TwoCategory where

open import GpdCont.Prelude
open import GpdCont.GroupoidContainer.WildCat renaming (GContCat to GroupoidContainerWildCat)
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.TwoDiscrete using (TwoDiscrete)

open import GpdCont.GroupoidContainer.Morphism using (isGroupoidGContMorphism)

GroupoidContainerCat : (ℓ : Level) → TwoCategory (ℓ-suc ℓ) ℓ ℓ
GroupoidContainerCat ℓ = TwoDiscrete (GroupoidContainerWildCat ℓ) λ _ _ → isGroupoidGContMorphism
