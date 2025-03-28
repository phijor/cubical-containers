module GpdCont.Prelude.Level where

open import Agda.Primitive using (LevelUniv)
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.FromNat public
open import Cubical.Core.Primitives

ℓ# : (n : Nat) → Level
ℓ# zero = ℓ-zero
ℓ# (suc n) = ℓ-suc (ℓ# n)

instance
  NumberLevel : Number Level
  NumberLevel .Number.Constraint n = ⊤
  NumberLevel .Number.fromNat n = ℓ# n

LevelTele : (n : Nat) → LevelUniv
LevelTele zero = Level
LevelTele (suc n) = Level → LevelTele n

ℓMax : {n : Nat} → LevelTele n
ℓMax {n = 0} = ℓ-zero
ℓMax {n = 1} = λ ℓ → ℓ
ℓMax {n = suc (suc n)} ℓ₀ ℓ₁ = ℓMax {n = suc n} (ℓ-max ℓ₀ ℓ₁)

ℓ-of : ∀ {ℓ} {A : Type ℓ} (a : A) → Level
ℓ-of {ℓ} _ = ℓ
