module GpdCont.Prelude where

open import GpdCont.RecordEquiv public

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function
  using (const ; _∘_ ; _$_ ; curry ; uncurry)
  renaming (idfun to id)
  public
open import Cubical.Foundations.Structure public using (⟨_⟩ ; str)
open import Cubical.Foundations.Equiv using (_≃_) renaming (_■ to _≃∎) public

open import Cubical.Data.Nat.Literals public

module _ where
  infixr 0 _≃⟨⟩_
  _≃⟨⟩_ : ∀ {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'} → A ≃ B → A ≃ B
  A ≃⟨⟩ e = e

module LevelNumber where
  open import Agda.Builtin.Nat
  open import Agda.Builtin.Unit
  open import Agda.Builtin.FromNat public

  ℓ# : (n : Nat) → Level
  ℓ# zero = ℓ-zero
  ℓ# (suc n) = ℓ-suc (ℓ# n)

  instance
    NumberLevel : Number Level
    NumberLevel .Number.Constraint n = ⊤
    NumberLevel .Number.fromNat n = ℓ# n

open LevelNumber public
