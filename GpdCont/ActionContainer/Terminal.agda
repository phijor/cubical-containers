open import GpdCont.Prelude
open import GpdCont.Univalence using (ua→)
open import GpdCont.ActionContainer.Base
open import GpdCont.ActionContainer.Morphism hiding (mkMorphism-syntax)
open import GpdCont.ActionContainer.Transformation
open import GpdCont.HomotopySet using (UnitSet ; EmptySet)
open import GpdCont.GroupAction.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels as HLevels using (hSet)
open import Cubical.Data.Empty as EmptyType using (⊥*)
open import Cubical.Data.Unit as UnitType using (Unit*)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (GroupIso→GroupHom ; invGroupIso ; makeIsGroupHom)
open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup ; contrGroupIsoUnit)

-- open ActionContainerMorphism using (Morphism ; mkMorphism)
-- open Transformation using (Transformation ; Transformationᴰ ; TransformationP)

module GpdCont.ActionContainer.Terminal (ℓ : Level) where

Shape : hSet ℓ
Shape = UnitSet ℓ

Pos : ⟨ Shape ⟩ → hSet ℓ
Pos _ = EmptySet ℓ

private
  isContr𝔖0 : isContr (⊥* {ℓ} ≃ ⊥*)
  isContr𝔖0 .fst = idEquiv _
  isContr𝔖0 .snd e = equivEq $ funExt λ ()

  UnitHom→ : ∀ {ℓ'} (G : Group ℓ') → GroupHom (UnitGroup {ℓ}) G
  UnitHom→ G .fst _ = str G .GroupStr.1g
  UnitHom→ G .snd = makeIsGroupHom λ _ _ → sym $ str G .GroupStr.·IdL _

  →UnitHom : ∀ {ℓ'} (G : Group ℓ') → GroupHom G (UnitGroup {ℓ})
  →UnitHom G .fst _ = tt*
  →UnitHom G .snd = makeIsGroupHom λ _ _ → refl

SymmGroup : ⟨ Shape ⟩ → Group ℓ
SymmGroup _ = UnitGroup {ℓ}

symmAction : ∀ s → Action (SymmGroup s) (Pos s)
symmAction _ = GroupHom→Action $ UnitHom→ _

terminalContainer : ActionContainer ℓ
terminalContainer = mkActionContainer Shape Pos SymmGroup symmAction

terminalMorphism : (C : ActionContainer ℓ) → Morphism C terminalContainer
terminalMorphism C = (u ▷ (f , f-equivariant) ◁ φ) where
  open GpdCont.ActionContainer.Morphism C terminalContainer using (mkMorphism-syntax)

  module C = ActionContainer C

  u : C.Shape → Unit*
  u = const tt*

  f : (s : C.Shape) → ⊥* → C.Pos s
  f s ()

  φ : (s : C.Shape) → GroupHom (C.SymmGroup s) UnitGroup
  φ s = →UnitHom (C.SymmGroup s)

  f-equivariant : ∀ s g → (equivFun (C.action g) ∘ (f s)) ≡ (f s ∘ id ⊥*)
  f-equivariant s g = funExt λ ()

module _ {C : ActionContainer ℓ} (F : Morphism C terminalContainer) where
  -- terminalTransformationP : TransformationP F (terminalMorphism C)
  -- terminalTransformationP .TransformationP.shape-path = refl
  -- terminalTransformationP .TransformationP.conjugator₀ _ = tt*
  -- terminalTransformationP .TransformationP.conjugator₁ _ = tt*
  -- terminalTransformationP .TransformationP.conjugator-path = refl {x = λ s → tt*}
  -- terminalTransformationP .TransformationP.is-conjugate s = refl {x = tt*}
  -- terminalTransformationP .TransformationP.is-pos-equiv s = ua→ λ ()

  -- terminalTransformation : Transformation F (terminalMorphism C)
  -- terminalTransformation = Transformation.TransformationP→Transformation terminalTransformationP

  terminalTransformation : Transformation F (terminalMorphism C)
  terminalTransformation = Transformation.refl-shape (const tt*) _ _ λ where
    .Transformationᴰ.conjugator → const tt*
    .Transformationᴰ.is-conjugate s g → refl {x = tt*}
    .Transformationᴰ.is-pos-equiv s → funExt λ ()

  isPropTerminalTransformation : isProp (Transformation F (terminalMorphism C))
  isPropTerminalTransformation x y = {! !}

  -- isPropTerminalTransformationP : isProp (TransformationP F (terminalMorphism C))
  -- isPropTerminalTransformationP α β i .TransformationP.shape-path = refl {x = const tt*}
  -- isPropTerminalTransformationP α β i .TransformationP.conjugator₀ s = tt*
  -- isPropTerminalTransformationP α β i .TransformationP.conjugator₁ s = tt*
  -- isPropTerminalTransformationP α β i .TransformationP.conjugator-path = refl {x = λ s → tt*}
  -- isPropTerminalTransformationP α β i .TransformationP.is-conjugate g = refl {x = tt*}
  -- isPropTerminalTransformationP α β i .TransformationP.is-pos-equiv = {! !}

{-
  universalProperty : isContr (TransformationP (initMorphism C) F)
  universalProperty = inhProp→isContr initialTransformationP isPropInitTransformationP
  -}
