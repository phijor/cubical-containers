module GpdCont.Connectivity where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Surjection using (isSurjection ; isPropIsSurjection)
open import Cubical.Data.Sigma.Properties as Sigma using ()
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.Truncation as Tr using (∥_∥_)
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level
    A B : Type ℓ
    f : A → B

isPathConnected : (A : Type ℓ) → Type ℓ
isPathConnected A = isContr ∥ A ∥₂

isPathConnectedFun : (f : A → B) → Type _
isPathConnectedFun {B} f = (b : B) →  isPathConnected (fiber f b)

isPropIsConnected : ∀ {n : HLevel} → isProp (isConnected n A)
isPropIsConnected = isPropIsContr

isPropIsConnectedFun : ∀ {n : HLevel} {f : A → B} → isProp (isConnectedFun n f)
isPropIsConnectedFun = isPropΠ λ _ → isPropIsConnected

merelyInh≃is1Connected : ∥ A ∥₁ ≃ isConnected 1 A
merelyInh≃is1Connected {A} =
  ∥ A ∥₁ ≃⟨ Tr.propTrunc≃Trunc1 ⟩
  ∥ A ∥ 1 ≃⟨ invEquiv $ Sigma.Σ-contractSnd (λ p → isContrΠ λ q → isProp→isContrPath (Tr.isOfHLevelTrunc 1) p q) ⟩
  isConnected 1 A ≃∎

isSurjection≃is1ConnectedFun : (f : A → B) → isSurjection f ≃ isConnectedFun 1 f
isSurjection≃is1ConnectedFun f = equivΠCod λ b → merelyInh≃is1Connected
