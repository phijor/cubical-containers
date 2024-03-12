module GpdCont.GroupAction where

open import GpdCont.Prelude
open import GpdCont.Groups.Base

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

record _-Set {ℓ} (G : Group ℓ) : Type (ℓ-suc ℓ) where
  private
    module G = GroupStr (str G)

  field
    action : ⟨ G ⟩ → hSet ℓ

  _⦅_⦆ : (g : ⟨ G ⟩) → Type ℓ
  _⦅_⦆ g = ⟨ action g ⟩

  is-set-⦅_⦆ : ∀ g → isSet (_⦅_⦆ g)
  is-set-⦅_⦆ = str ∘ action

  -- _· : Type ℓ
  -- _· = _⦅_⦆ G.pt

  -- is-set-· : isSet _·
  -- is-set-· = is-set-⦅_⦆ G.pt
