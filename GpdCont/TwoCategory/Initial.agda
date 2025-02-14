open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

module GpdCont.TwoCategory.Initial {ℓo ℓh ℓr} (C : TwoCategory ℓo ℓh ℓr) where

open import Cubical.Foundations.HLevels

private
  module C = TwoCategory C

isInitial : (x : C.ob) → Type _
isInitial x = ∀ (y : C.ob) (f g : C.hom x y) → isContr (C.rel f g)

isPropIsInitial : ∀ x → isProp (isInitial x)
isPropIsInitial x = isPropΠ3 λ y f g → isPropIsContr

Initial : Type _
Initial = Σ[ x ∈ C.ob ] isInitial x

isOfHLevelSucInitial : (n : HLevel) → isOfHLevel (suc n) C.ob → isOfHLevel (suc n) Initial
isOfHLevelSucInitial n is-trunc-ob = isOfHLevelΣ (suc n) is-trunc-ob (isProp→isOfHLevelSuc n ∘ isPropIsInitial)
