module GpdCont.ActionContainer.Sum where

open import GpdCont.Prelude
open import GpdCont.ActionContainer.Abstract
open import GpdCont.ActionContainer.Morphism
open import GpdCont.HomotopySet using (_⊎Set_ ; ΣSet)
open import GpdCont.GroupAction.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (hSet)
open import Cubical.Data.Sum as TypeSum using ()
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom)

private
  variable
    ℓ : Level

module Sum (C D : ActionContainer ℓ) where
  private
    module C = ActionContainer C
    module D = ActionContainer D

  Shape : hSet _
  Shape = C.ShapeSet ⊎Set D.ShapeSet

  Pos : ⟨ Shape ⟩ → hSet _
  Pos = TypeSum.rec C.PosSet D.PosSet

  SymmGroup : ⟨ Shape ⟩ → Group _
  SymmGroup = TypeSum.rec C.SymmGroup D.SymmGroup

  symmAction : ∀ s → Action (SymmGroup s) (Pos s)
  symmAction = TypeSum.elim C.symmAction D.symmAction

  self : ActionContainer ℓ
  self = mkActionContainer Shape Pos SymmGroup symmAction

  inlMorphism : Morphism C self
  inlMorphism = mkMorphism C self
    TypeSum.inl
    (λ s → id _)
    (λ s → id _)
    (λ _ _ → refl)
    (λ s → idGroupHom .snd)

  inrMorphism : Morphism D self
  inrMorphism = mkMorphism D self
    TypeSum.inr
    (λ s → id _)
    (λ s → id _)
    (λ _ _ → refl)
    (λ s → idGroupHom .snd)

  -- inrTransformation : isContr (Morphism D self)
  -- inrTransformation = ?

open Sum using () renaming (self to _⊕_) public

module IndexedSum {J : Type ℓ} (is-set-J : isSet J) (C : J → ActionContainer ℓ) where
  open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)
  open import GpdCont.GroupAction.Pi using (ΠAction)

  private
    module C (j : J) = ActionContainer (C j)

    JSet : hSet _
    JSet .fst = J
    JSet .snd = is-set-J

  Shape : hSet ℓ
  Shape = ΣSet JSet C.ShapeSet

  Pos : ⟨ Shape ⟩ → hSet ℓ
  Pos = uncurry C.PosSet

  Symm : ⟨ Shape ⟩ → Group _
  Symm = uncurry C.SymmGroup

  symmAction : ∀ s → Action (Symm s) (Pos s)
  symmAction = uncurry C.symmAction

  self : ActionContainer ℓ
  self = mkActionContainer Shape Pos Symm symmAction

  module _ {j : J} where
    inShape : C.Shape j → ⟨ Shape ⟩
    inShape s = j , s

    inPos : (s : C.Shape j) → C.Pos j s → C.Pos j s
    inPos s = id _

    inSymm : ∀ s → C.Symm j s → C.Symm j s
    inSymm s = id _

    inMorphism : Morphism (C j) self
    inMorphism = mkMorphism (C j) self inShape inPos inSymm
      (λ s g → refl)
      (λ s → idGroupHom .snd)
