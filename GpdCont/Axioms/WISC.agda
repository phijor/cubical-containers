module GpdCont.Axioms.WISC where

open import GpdCont.Prelude

open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.Functions.Surjection

private
  variable
    ℓ : Level

isWISC : ∀ {C : Type ℓ} (E : C → Type ℓ) (Y : Type ℓ) → Type (ℓ-suc ℓ)
isWISC {ℓ} {C} E Y = (X : Type ℓ) → (q : X → Y) → isSurjection q → Σ[ c ∈ C ] Σ[ f ∈ (E c → X) ] isSurjection (q ∘ f)

WISC : (ℓ : Level) → Type (ℓ-suc ℓ)
WISC ℓ = {A : Type ℓ} (B : A → Type ℓ) → ∥ Σ[ C ∈ Type ℓ ] Σ[ E ∈ (C → Type ℓ) ] (∀ a → isWISC E (B a)) ∥₁
