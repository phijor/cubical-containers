module GpdCont.GroupoidContainer.Base where

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
