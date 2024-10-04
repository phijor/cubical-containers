module GpdCont.ActionContainer.CyclicLists where

open import GpdCont.Prelude
open import GpdCont.ActionContainer.Abstract

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)

open import Cubical.HITs.FreeGroup as FG using (FreeGroup)

private
  ℤ : Type
  ℤ = FreeGroup Unit

  ℤGroup : Group ℓ-zero
  ℤGroup = FG.freeGroupGroup Unit

  ℤrec : ∀ {ℓ} {G : Group ℓ} → ⟨ G ⟩ → GroupHom ℤGroup G
  ℤrec g = FG.rec $ const g

Cyc : ActionContainer ℓ-zero
Cyc = mkActionContainer (ℕ , isSetℕ) {! !} {! !} {! !}
