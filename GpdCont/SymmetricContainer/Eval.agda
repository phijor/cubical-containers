open import GpdCont.SymmetricContainer.Base

module GpdCont.SymmetricContainer.Eval {ℓ} (G : GCont ℓ) where

open import GpdCont.Prelude
open import GpdCont.Polynomial as Poly using (Polynomial)

open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Properties as Sigma using (map-snd)

open GCont G

⟦_⟧ᵗ : Type ℓ → Type ℓ
⟦_⟧ᵗ = Polynomial Shape Pos

open Polynomial using (shape ; label) public

opaque
  isGroupoid-⟦_⟧ᵗ : ∀ {X} → isGroupoid X → isGroupoid (⟦_⟧ᵗ X)
  isGroupoid-⟦_⟧ᵗ = Poly.isOfHLevelPolynomial 3 is-groupoid-shape

⟦_⟧ : hGroupoid ℓ → hGroupoid ℓ
⟦_⟧ (X , is-groupoid-X) .fst = ⟦ X ⟧ᵗ
⟦_⟧ (X , is-groupoid-X) .snd = isGroupoid-⟦_⟧ᵗ is-groupoid-X

⟦-⟧ᵗ-Path : ∀ {X : Type ℓ} {p q : ⟦_⟧ᵗ X}
  → (shape-path : shape p ≡ shape q)
  → (label-path : PathP (λ i → Pos (shape-path i) → X) (label p) (label q))
  → p ≡ q
⟦-⟧ᵗ-Path = Poly.Polynomial≡

⟦-⟧-Path : ∀ {X : hGroupoid ℓ} {p q : ⟨ ⟦_⟧ X ⟩}
  → (shape-path : shape p ≡ shape q)
  → (label-path : PathP (λ i → Pos (shape-path i) → ⟨ X ⟩) (label p ) (label q))
  → p ≡ q
⟦-⟧-Path = ⟦-⟧ᵗ-Path

module Map = Poly.Map Shape Pos

⟦_⟧-map : ∀ (X Y : hGroupoid ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) → ⟨ ⟦_⟧ X ⟩ → ⟨ ⟦_⟧ Y ⟩
⟦_⟧-map _ _ = Map.map

⟦_⟧-map-id : (X : hGroupoid ℓ) → ⟦_⟧-map X X (id ⟨ X ⟩) ≡ id ⟨ ⟦_⟧ X ⟩
⟦_⟧-map-id X = Map.map-id ⟨ X ⟩

⟦_⟧-map-comp : ∀ (X Y Z : hGroupoid ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) (g : ⟨ Y ⟩ → ⟨ Z ⟩) → ⟦_⟧-map X Z (g ∘ f) ≡ ⟦_⟧-map Y Z g ∘ ⟦_⟧-map X Y f
⟦_⟧-map-comp _ _ _ = Map.map-comp
