open import GpdCont.Prelude hiding (_▷_)
open import GpdCont.GroupAction.Base

open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base

module GpdCont.GroupAction.Orbit {ℓ} {G : Group ℓ} {X : hSet ℓ} (σ : Action G X) where

open import Cubical.HITs.SetQuotients as SQ using (_/_)

private
  module G = GroupStr (str G)
  open module σ = Action σ using (_▷_)

_∼_ : (x y : ⟨ X ⟩) → Type ℓ
x ∼ y = ∃[ g ∈ ⟨ G ⟩ ] g ▷ x ≡ y

∼-intro-right : (g : ⟨ G ⟩) (x : ⟨ X ⟩) → x ∼ (g ▷ x)
∼-intro-right g x = ∃-intro g goal where
  goal : g ▷ x ≡ g ▷ x
  goal = refl

Orbit : Type _
Orbit = ⟨ X ⟩ / _∼_

[_] : ⟨ X ⟩ → Orbit
[_] = SQ.[_]

[_∣_] : ⟨ X ⟩ → Orbit
[_∣_] = λ x → [ x ]

∼→≡ : ∀ {x y} → x ∼ y → [ x ] ≡ [ y ]
∼→≡ = SQ.eq/ _ _

act→≡ : ∀ g x → [ x ] ≡ [ g ▷ x ]
act→≡ g x = ∼→≡ (∼-intro-right g x)

isSetOrbit : isSet Orbit
isSetOrbit = SQ.squash/

OrbitSet : hSet _
OrbitSet .fst = Orbit
OrbitSet .snd = isSetOrbit
