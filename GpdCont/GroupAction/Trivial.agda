module GpdCont.GroupAction.Trivial where

open import GpdCont.Prelude
open import GpdCont.GroupAction.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base

private
  variable
    ℓ : Level

open Action

trivialAction : (G : Group ℓ) (X : hSet ℓ) → Action G X
trivialAction G X .action = const $ idEquiv ⟨ X ⟩
trivialAction G X .pres· _ _ = equivEq refl
