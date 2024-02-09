module GpdCont.Partition where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

record Partition {ℓ} (A : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    Idx : Type ℓ
    Part : Idx → Type ℓ

    part-equiv : A ≃ Σ Idx Part

    is-set-idx : isSet Idx
    is-pointed-connected : ∀ i → Σ[ pt ∈ Part i ] ∀ x → ∥ x ≡ pt ∥₁

  part· : (i : Idx) → Part i
  part· i = is-pointed-connected i .fst

  pt : Idx → A
  pt i = invEq part-equiv (i , part· i)
