module GpdCont.SymmetryContainer where

open import GpdCont.Prelude
open import GpdCont.Group
open import GpdCont.GroupAction
-- open import GpdCont.GroupoidContainer as GC using (GCont)
open import GpdCont.Groupoid using (Skeleton)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

record SymmetryContainer (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    shape-skeleton : Skeleton ℓ

  open Skeleton shape-skeleton public
    using
      ( Index
      ; Component
      ; is-set-index
      ; group-str-component
      ; ComponentGroup
      )
    renaming (Total to Shape)

  field
    PosSet : ∀ idx → (ComponentGroup idx) -Set

  module _ (idx : Index) where
    open GroupStr (group-str-component idx) public
      renaming (is-groupoid to isGroupoidPart ; is-connected to isConnectedPart)

  isGroupoidShape : isGroupoid Shape
  isGroupoidShape = isGroupoidΣ (isSet→isGroupoid is-set-index) isGroupoidPart

  private
    module PosUncurry ((idx , part) : Shape) where
      private
        module P = _-Set (PosSet idx)

      Pos : Type _
      Pos = P._⦅_⦆ part

      isSetPos : isSet Pos
      isSetPos = P.is-set-⦅ part ⦆

  open PosUncurry public using (Pos ; isSetPos)

