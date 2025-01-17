open import GpdCont.Experimental.Coffin.Base

module GpdCont.Experimental.Coffin.Eval {ℓ} (C : Coffin ℓ) where
-- TODO: This should ideally do the following:
-- import GpdCont.Coffin.GroupoidContainerInclusion as Inc
-- open import GpdCont.GroupoidContainer.Eval (Inc.Coffin→GroupoidContainer C) public
--
-- But opaque definitions an re-exports are weird and stuff doesn't reduce.

open import GpdCont.Prelude
open import Cubical.Foundations.HLevels

open module C = Coffin C
opaque
  ⟦_⟧ᵗ : Type ℓ → Type ℓ
  ⟦_⟧ᵗ X = Σ[ s ∈ Shape ] (Pos s → X)

  mk⟦_⟧ᵗ : ∀ {X} → Σ[ s ∈ Shape ] (Pos s → X) → ⟦_⟧ᵗ X
  mk⟦_⟧ᵗ x = x

  shape : ∀ {X} → ⟦_⟧ᵗ X → Shape
  shape (s , _) = s

  label : ∀ {X} → (x : ⟦_⟧ᵗ X) → Pos (shape x) → X
  label (_ , v) = v

  isGroupoid-⟦_⟧ᵗ : ∀ {X} → isGroupoid X → isGroupoid (⟦_⟧ᵗ X)
  isGroupoid-⟦_⟧ᵗ is-groupoid-X = isGroupoidΣ C.is-groupoid-shape λ s → isGroupoidΠ (const is-groupoid-X)

  ⟦_⟧ : hGroupoid ℓ → hGroupoid ℓ
  ⟦_⟧ X .fst = ⟦_⟧ᵗ ⟨ X ⟩
  ⟦_⟧ X .snd = isGroupoid-⟦_⟧ᵗ (str X)

  ⟦-⟧ᵗ-Path : ∀ {X : Type ℓ} {x y : ⟦_⟧ᵗ X}
    → (p : shape x ≡ shape y)
    → (q : PathP (λ i → Pos (p i) → X) (label x) (label y))
    → x ≡ y
  ⟦-⟧ᵗ-Path p q i .fst = p i
  ⟦-⟧ᵗ-Path p q i .snd = q i

