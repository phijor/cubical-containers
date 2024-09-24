module GpdCont.ActionContainer.SingleShape where

open import GpdCont.Prelude
open import GpdCont.GroupAction.Base
open import GpdCont.ActionContainer.Abstract

open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Algebra.Group.Base

module _ {ℓ} (P : hSet ℓ) (G : Group ℓ) (σ : Action G P) where
  open ActionContainer
  mkSingleShapeCont : ActionContainer ℓ
  mkSingleShapeCont = mkActionContainer (Unit* , isSetUnit*) (λ _ → P) (λ _ → G) (λ _ → σ)
