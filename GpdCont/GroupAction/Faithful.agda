module GpdCont.GroupAction.Faithful where

open import GpdCont.Prelude

open import GpdCont.GroupAction.Base

open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms using (isMono)

private
  variable
    ℓ : Level
    G : Group ℓ
    X : hSet ℓ
    σ : Action G X

isFaithful : (σ : Action G X) → Type _
isFaithful {G} σ = ∀ {g h : ⟨ G ⟩} → action g ≡ action h → g ≡ h where
  open Action σ using (action)

isPropIsFaithful : (σ : Action G X) → isProp (isFaithful σ)
isPropIsFaithful {G} σ = isPropImplicitΠ2 λ g h → isProp→ (G.is-set g h) where
  module G = GroupStr (str G)

isFaithful→isGroupHomMono : isFaithful σ → isMono (Action→GroupHom σ)
isFaithful→isGroupHomMono ff = ff
