module GpdCont.GroupoidContainer where

open import GpdCont.Prelude
open import Cubical.Foundations.HLevels

record GCont (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Shape : Type ℓ
    Pos : Shape → Type ℓ

  field
    is-groupoid-shape : isGroupoid Shape
    is-set-pos : ∀ s → isSet (Pos s)

  opaque
    ShapeGroupoid : hGroupoid ℓ
    ShapeGroupoid .fst = Shape
    ShapeGroupoid .snd = is-groupoid-shape

    PosSet : (s : Shape) → hSet ℓ
    PosSet s .fst = Pos s
    PosSet s .snd = is-set-pos s

module Eval {ℓ} (G : GCont ℓ) where
  open GCont G
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
    isGroupoid-⟦_⟧ᵗ is-groupoid-X = isGroupoidΣ is-groupoid-shape λ s → isGroupoidΠ (const is-groupoid-X)

    ⟦_⟧ : hGroupoid ℓ → hGroupoid ℓ
    ⟦_⟧ X .fst = ⟦_⟧ᵗ ⟨ X ⟩
    ⟦_⟧ X .snd = isGroupoid-⟦_⟧ᵗ (str X)

    ⟦-⟧ᵗ-Path : ∀ {X : Type ℓ} {x y : ⟦_⟧ᵗ X}
      → (p : shape x ≡ shape y)
      → (q : PathP (λ i → Pos (p i) → X) (label x) (label y))
      → x ≡ y
    ⟦-⟧ᵗ-Path p q i .fst = p i
    ⟦-⟧ᵗ-Path p q i .snd = q i

