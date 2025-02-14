module GpdCont.SymmetricContainer.Base where

open import GpdCont.Prelude
open import Cubical.Foundations.HLevels

record SymmetricContainer (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Shape : Type ℓ
    Pos : Shape → Type ℓ

  field
    is-groupoid-shape : isGroupoid Shape
    is-set-pos : ∀ s → isSet (Pos s)

  ShapeGroupoid : hGroupoid ℓ
  ShapeGroupoid .fst = Shape
  ShapeGroupoid .snd = is-groupoid-shape

  PosSet : (s : Shape) → hSet ℓ
  PosSet s .fst = Pos s
  PosSet s .snd = is-set-pos s

mkSymmetricContainer : ∀ {ℓ} → (S : hGroupoid ℓ) (P : ⟨ S ⟩ → hSet ℓ) → SymmetricContainer ℓ
mkSymmetricContainer S P .SymmetricContainer.Shape = ⟨ S ⟩
mkSymmetricContainer S P .SymmetricContainer.Pos = ⟨_⟩ ∘ P
mkSymmetricContainer S P .SymmetricContainer.is-groupoid-shape = str S
mkSymmetricContainer S P .SymmetricContainer.is-set-pos = str ∘ P

syntax mkSymmetricContainer S (λ s → P) = [ s ∈ S ◁ P ]
