module GpdCont.StrictGroupoid.HomotopyGroup where

open import GpdCont.Prelude
open import GpdCont.Connectivity

open import GpdCont.StrictGroupoid.Base

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Properties using (hasSection)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)

open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

isHGroup : StrictGroupoid ℓ → Type ℓ
isHGroup G = isPathConnected ⟨ G ⟩

isPropIsHGroup : (G : StrictGroupoid ℓ) → isProp (isHGroup G)
isPropIsHGroup G = isPropIsPathConnected ⟨ G ⟩

hGroup : (ℓ : Level) → Type (ℓ-suc ℓ)
hGroup ℓ = Σ[ G ∈ StrictGroupoid ℓ ] isHGroup G

hGroup≡ : ∀ {G H : hGroup ℓ} → G .fst ≡ H .fst → G ≡ H
hGroup≡ = Σ≡Prop isPropIsHGroup
