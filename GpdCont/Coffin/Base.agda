module GpdCont.Coffin.Base where

open import GpdCont.Prelude
open import GpdCont.Groups.Base
open import GpdCont.GroupAction
open import GpdCont.Groupoid using (Skeleton)

open import Cubical.Foundations.HLevels using (isGroupoidΣ ; isSet→isGroupoid ; hSet)

record Coffin (ℓ : Level) : Type (ℓ-suc ℓ) where
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

  PosSet-pt : Index → hSet ℓ
  PosSet-pt idx = PosSet idx ._-Set.action (shape-skeleton .Skeleton.component idx)
