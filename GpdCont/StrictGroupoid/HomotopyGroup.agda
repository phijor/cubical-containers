module GpdCont.StrictGroupoid.HomotopyGroup where

open import GpdCont.Prelude
open import GpdCont.Connectivity
open import GpdCont.StrictGroupoid.Base

isHGroup : ∀ {ℓ} (G : StrictGroupoid ℓ) → Type _
isHGroup G = isPathConnected ⟨ G ⟩

isPropIsHGroup : ∀ {ℓ} (G : StrictGroupoid ℓ) → isProp (isHGroup G)
isPropIsHGroup G = isPropIsPathConnected ⟨ G ⟩

hGroup : (ℓ : Level) → Type _
hGroup ℓ = Σ[ G ∈ StrictGroupoid ℓ ] isHGroup G
