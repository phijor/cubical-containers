module GpdCont.Analytic where

open import GpdCont.Prelude

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Nat.Base

record GroupStr {ℓ} (G : Type ℓ) : Type ℓ where
  field
    pt : G
    is-connected : isContr ∥ G ∥₂

Group : (ℓ : Level) → Type _
Group ℓ = TypeWithStr ℓ GroupStr

private
  variable
    ℓ : Level

record [_]Set (G : Group ℓ) : Type (ℓ-suc ℓ) where
  private
    module G = GroupStr (str G)

  field
    action : ⟨ G ⟩ → hSet ℓ

  _· : Type ℓ
  _· = ⟨ action G.pt ⟩

  is-set-· : isSet _·
  is-set-· = str $ action G.pt

Prod : (G : Group ℓ) → (X Y : [ G ]Set) → [ G ]Set
Prod G X Y = X⊗Y where

  X⊗Y : [ G ]Set
  X⊗Y .[_]Set.action = {! !}

private
  variable
    G : Group ℓ

open [_]Set

_⇒_ : {G : Group ℓ} (X : [ G ]Set) → (A : hSet ℓ) → [ G ]Set
_⇒_ X A .action γ = (⟨ X .action γ ⟩ → ⟨ A ⟩) , isSet→ (str A)

_[_] : ∀ {G : Group ℓ} (F : hSet ℓ → hSet ℓ) → (X : [ G ]Set) → [ G ]Set
(F [ X ]) .action = F ∘ X .action
