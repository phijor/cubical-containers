open import GpdCont.Prelude
open import GpdCont.ActionContainer.Abstract
open import GpdCont.HomotopySet using (EmptySet)
open import GpdCont.GroupAction.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (hSet ; inhProp→isContr)
open import Cubical.Data.Empty as EmptyType using ()
open import Cubical.Algebra.Group.Base

open ActionContainerMorphism using (Morphism ; mkMorphism)
open Transformation using (Transformation ; Transformationᴰ ; TransformationP)

module GpdCont.ActionContainer.Initial (ℓ : Level) where

Shape : hSet ℓ
Shape = EmptySet ℓ

Pos : ⟨ Shape ⟩ → hSet ℓ
Pos = EmptyType.rec*

SymmGroup : ⟨ Shape ⟩ → Group ℓ
SymmGroup = EmptyType.rec*

symmAction : ∀ s → Action (SymmGroup s) (Pos s)
symmAction = EmptyType.elim*

InitContainer : ActionContainer ℓ
InitContainer = mkActionContainer Shape Pos SymmGroup symmAction

initMorphism : (C : ActionContainer ℓ) → Morphism InitContainer C
initMorphism C =
  let open ActionContainerMorphism InitContainer C using (mkMorphism-syntax)
  in ( EmptyType.rec* ▷ (EmptyType.elim* , EmptyType.elim*) ◁ EmptyType.elim*)

module _ {C : ActionContainer ℓ} (F : Morphism InitContainer C) where
  initialTransformationP : TransformationP (initMorphism C) F
  initialTransformationP .TransformationP.shape-path i ()
  initialTransformationP .TransformationP.conjugator₀ ()
  initialTransformationP .TransformationP.conjugator₁ ()
  initialTransformationP .TransformationP.conjugator-path i ()
  initialTransformationP .TransformationP.is-conjugate {s = ()}
  initialTransformationP .TransformationP.is-pos-equiv ()

  initialTransformation : Transformation (initMorphism C) F
  initialTransformation = Transformation.TransformationP→Transformation initialTransformationP

  isPropInitTransformationP : isProp (TransformationP (initMorphism C) F)
  isPropInitTransformationP α β i .TransformationP.shape-path j ()
  isPropInitTransformationP α β i .TransformationP.conjugator₀ ()
  isPropInitTransformationP α β i .TransformationP.conjugator₁ ()
  isPropInitTransformationP α β i .TransformationP.conjugator-path j ()
  isPropInitTransformationP α β i .TransformationP.is-conjugate {s = ()}
  isPropInitTransformationP α β i .TransformationP.is-pos-equiv ()

  universalProperty : isContr (TransformationP (initMorphism C) F)
  universalProperty = inhProp→isContr initialTransformationP isPropInitTransformationP
