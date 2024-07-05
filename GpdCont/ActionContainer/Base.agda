module GpdCont.ActionContainer.Base where

open import GpdCont.Prelude
open import GpdCont.Groups.Base
open import GpdCont.GroupAction

open import Cubical.Foundations.HLevels

record ActionCont (ℓ : Level) : Type (ℓ-suc ℓ) where
  no-eta-equality
  field
    ShapeSet : hSet ℓ

  Shape : Type ℓ
  Shape = ⟨ ShapeSet ⟩

  field
    SymmGroup : Shape → Group ℓ
    SymmAction : (s : Shape) → Action (SymmGroup s)

  open Action using (_⋆Set)
  
  Pos : Shape → hSet ℓ
  Pos s = SymmAction s ⋆Set
