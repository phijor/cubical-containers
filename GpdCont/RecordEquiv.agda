module GpdCont.RecordEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism hiding (iso)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_$_)
open import Cubical.Reflection.StrictEquiv public
open import Cubical.Reflection.RecordEquiv public

open Iso

record RecordToΣ {ℓ} (R : Type ℓ) {S : Type ℓ} : Type (ℓ-suc ℓ) where
  constructor toΣ
  field
    isoΣ : Iso R S
    @(tactic strictEquivMacro (isoΣ .fun) (isoΣ .inv)) {equivΣ} : R ≃ S
  
open RecordToΣ ⦃...⦄

infix 1.5 _asΣ
_asΣ : ∀ {ℓ} (R : Type ℓ) {S : Type ℓ} → ⦃ RecordToΣ R {S} ⦄ → Type ℓ
_asΣ R {S = S} = S

_IsoΣ : ∀ {ℓ} (R : Type ℓ) {S : Type ℓ} → ⦃ RecordToΣ R {S} ⦄ → Iso R S
R IsoΣ = isoΣ

_≃Σ : ∀ {ℓ} (R : Type ℓ) {S : Type ℓ} → ⦃ RecordToΣ R {S} ⦄ → R ≃ S
R ≃Σ = equivΣ

cast→Σ : ∀ {ℓ} {R : Type ℓ} {S : Type ℓ} → ⦃ RecordToΣ R {S} ⦄ → R → S
cast→Σ = isoΣ .fun

cast←Σ : ∀ {ℓ} {R : Type ℓ} {S : Type ℓ} → ⦃ RecordToΣ R {S} ⦄ → S → R
cast←Σ = isoΣ .inv

recordIsOfHLevel : ∀ {ℓ} {R S : Type ℓ} → ⦃ RecordToΣ R {S} ⦄ → (n : HLevel) → isOfHLevel n S → isOfHLevel n R
recordIsOfHLevel n = isOfHLevelRetractFromIso n isoΣ
