open import GpdCont.Prelude

module GpdCont.SymmetricContainer.Substitution (ℓ : Level) where

open import GpdCont.HLevels
open import GpdCont.Univalence
open import GpdCont.SymmetricContainer.Base

open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

Subst : (F G : SymmetricContainer ℓ) → SymmetricContainer ℓ
Subst F G = F[G] where
  module F = SymmetricContainer F
  module G = SymmetricContainer G

  Shape : hGroupoid _
  Shape = Σʰ[ 3 ∣ s ∈ F.ShapeGroupoid ] (F.Pos s →₃ G.ShapeGroupoid)

  Pos : ⟨ Shape ⟩ → hSet _
  Pos (s , f) = Σʰ[ 2 ∣ p ∈ F.PosSet s ] G.PosSet (f p)

  F[G] : SymmetricContainer ℓ
  F[G] = mkSymmetricContainer Shape Pos

SubstId : ∀ F → Subst F Id ≡ F
SubstId F = SymmetricContainer≡ shape-path (ua→ pos-path) where
  module F = SymmetricContainer F
  module F[Id] = SymmetricContainer (Subst F Id)

  shape-equiv : F[Id].Shape ≃ F.Shape
  shape-equiv = Σ-contractSnd (λ s → isContrΠ λ _ → isContrUnit*)

  shape-path : F[Id].Shape ≡ F.Shape
  shape-path = ua shape-equiv

  pos-equiv : ∀ s* → F[Id].Pos s* ≃ F.Pos (equivFun shape-equiv s*)
  pos-equiv s* = Σ-contractSnd λ p → isContrUnit*

  pos-path : ∀ s* → F[Id].Pos s* ≡ F.Pos (equivFun shape-equiv s*)
  pos-path = ua ∘ pos-equiv
