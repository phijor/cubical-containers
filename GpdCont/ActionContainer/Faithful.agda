module GpdCont.ActionContainer.Faithful where

open import GpdCont.Prelude

open import GpdCont.ActionContainer.Abstract
open import GpdCont.ActionContainer.Category
open import GpdCont.GroupAction.Faithful using (isFaithful)

open import Cubical.Algebra.Group.Morphisms using (isInjective)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.PropertyOver using (PropertyOver)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.TotalCategory.Base using (∫C)

private
  variable
    ℓ : Level

isFaithfulContainer : (C : ActionContainer ℓ) → Type _
isFaithfulContainer C = ∀ s → isFaithful (symmAction s) where
  open ActionContainer C

ActFFᴰ : Categoryᴰ (Act {ℓ}) _ _
ActFFᴰ = PropertyOver Act isFaithfulContainer

ActFF : Category (ℓ-suc ℓ) ℓ
ActFF = ∫C {C = Act} ActFFᴰ
