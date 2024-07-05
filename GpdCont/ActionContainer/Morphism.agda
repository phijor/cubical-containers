module GpdCont.ActionContainer.Morphism where

open import GpdCont.Prelude
open import GpdCont.ActionContainer.Base
open import GpdCont.Groups.Homomorphism as GHom using (GroupHom)
open import GpdCont.GroupAction using (Equivariant ; Action ; pullbackAction)

private
  variable
    ℓ : Level

record ActionContMorphism {ℓ} (C D : ActionCont ℓ) : Type (ℓ-suc ℓ) where
  private
    module C = ActionCont C
    module D = ActionCont D

    G = C.SymmGroup
    H = D.SymmGroup

    P = C.SymmAction
    Q = D.SymmAction

  field
    shape : C.Shape → D.Shape
    symm : (s : C.Shape) → GroupHom (G s) (H $ shape s)

  CodomAction : ∀ s → Action (G s)
  CodomAction s = pullbackAction (symm s) (Q (shape s))

  private
    symm*Q = CodomAction

  field
    pos : ∀ (s : C.Shape) → Equivariant (symm*Q s) (P s)
