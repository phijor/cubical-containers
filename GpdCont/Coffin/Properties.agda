module GpdCont.Coffin.Properties where

open import GpdCont.Prelude
open import GpdCont.Coffin.Base
open import GpdCont.SetTruncation

open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.SetTruncation.Properties as ST using ()
open import Cubical.Data.Sigma

module _ {ℓ} (C : Coffin ℓ) where
  open module C = Coffin C using (Shape ; Index ; Component)

  TruncShape≃Index : ∥ Shape ∥₂ ≃ Index
  TruncShape≃Index =
    ∥ Shape ∥₂ ≃⟨⟩
    ∥ Σ[ k ∈ Index ] Component k ∥₂ ≃⟨ setTruncateFstΣ≃ C.is-set-index ⟩
    Σ[ k ∈ Index ] ∥ Component k ∥₂ ≃⟨ Σ-contractSnd C.isConnectedPart ⟩
    Index ≃∎
