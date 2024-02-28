module GpdCont.SetTruncation where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

private
  variable
    ℓA ℓB : Level
    A : Type ℓA
    B : A → Type ℓB

IsoSetTruncateFstΣ : isSet A → Iso ∥ Σ A B ∥₂ (Σ A (∥_∥₂ ∘ B))
IsoSetTruncateFstΣ {A} {B} is-set-A = go where
  isSetΣA∥B∥ : isSet (Σ A (∥_∥₂ ∘ B))
  isSetΣA∥B∥ = isSetΣ is-set-A λ a → ST.isSetSetTrunc
  go : Iso _ _
  go .Iso.fun = ST.rec isSetΣA∥B∥ λ { (a , b) → a , ST.∣ b ∣₂ }
  go .Iso.inv = uncurry λ a → ST.rec ST.isSetSetTrunc λ { b → ST.∣ a , b ∣₂ }
  go .Iso.rightInv = uncurry λ a → ST.elim (λ ∣b∣ → isProp→isSet (isSetΣA∥B∥ _ (a , ∣b∣))) λ _ → refl
  go .Iso.leftInv = ST.elim (λ ∣a,b∣ → isProp→isSet (ST.isSetSetTrunc _ ∣a,b∣)) λ _ → refl

setTruncateFstΣ≃ : isSet A → ∥ Σ A B ∥₂ ≃ (Σ A (∥_∥₂ ∘ B))
setTruncateFstΣ≃ = isoToEquiv ∘ IsoSetTruncateFstΣ
