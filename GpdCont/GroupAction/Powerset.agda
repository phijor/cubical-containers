{-# OPTIONS --lossy-unification #-}
open import GpdCont.Prelude hiding (_▷_)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Pi using (preCompAction)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Algebra.Group.Base
open import Cubical.Data.Sigma

module GpdCont.GroupAction.Powerset {ℓG ℓX}
  (G : Group ℓG)
  (X : hSet ℓX)
  (σ : Action G X)
  where

  private
    open module G = GroupStr (str G) using (_·_)

    module σ where
      open Action σ public
      open ActionProperties σ public

    open σ using (_▷_)

    ℙX : hSet _
    ℙX .fst = ℙ ⟨ X ⟩
    ℙX .snd = isSetℙ

    hPropSet : hSet (ℓ-suc ℓX)
    hPropSet .fst = hProp _
    hPropSet .snd = isSetHProp

  PowersetAction : Action G ℙX
  PowersetAction = preCompAction {G = G} {X = X} σ hPropSet
