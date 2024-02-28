module GpdCont.Lift where

open import GpdCont.Prelude hiding (Lift)

open import GpdCont.QuotientContainer as QC using (QCont)
open import GpdCont.GroupoidContainer as GC using (GCont)
open import GpdCont.Univalence as UA using (ua→ ; pathToEquiv ; ua)

open import Cubical.Data.Sigma.Base
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (isProp→SquareP ; flipSquare)
open import Cubical.HITs.GroupoidQuotients as GQ using (_//_)
open import Cubical.Functions.Embedding

module Lift {ℓ} (Q : QCont ℓ) where
  open QCont Q using (Shape ; Pos ; Symm ; _∼_ ; PosSet)

  open module Q = QCont Q using (_·_)

  open import Cubical.HITs.SetQuotients as SQ using (_/_)

  module ↑SymmElim (s : Shape) where
    open import GpdCont.Delooping using (module Delooping)

    open Delooping (s ∼ s) _·_ public
      renaming (𝔹 to ↑Symm ; isGroupoid𝔹 to isGroupoid-↑Symm)

  open ↑SymmElim
    using (↑Symm ; isGroupoid-↑Symm)
    public

  record ↑Shape : Type ℓ where
    constructor ↑⟨_,_⟩
    field
      ↓shape : Shape
      symm : ↑Symm ↓shape

  open ↑Shape public

  ↑shape : (s : Shape) → ↑Shape
  ↑shape s .↓shape = s
  ↑shape s .symm = ↑Symm.⋆
  
  ↑loop : ∀ {s : Shape} → s ∼ s → ↑shape s ≡ ↑shape s
  ↑loop r i .↓shape = _
  ↑loop r i .symm = ↑Symm.loop r i

  ↑loop-comp : ∀ {s} → (g h : s ∼ s) → compSquareFiller (↑loop g) (↑loop h) (↑loop (g · h))
  ↑loop-comp g h i j .↓shape = _
  ↑loop-comp g h i j .symm = ↑Symm.loop-comp g h i j

  unquoteDecl ↑ShapeIsoΣ = declareRecordIsoΣ ↑ShapeIsoΣ (quote ↑Shape)

  instance
    ↑ShapeToΣ : RecordToΣ ↑Shape
    ↑ShapeToΣ = toΣ ↑ShapeIsoΣ

  ↑Shape-uncurry : ∀ {ℓC} {C : (s : Shape) → ↑Symm s → Type ℓC}
    → (f : ∀ s σ → C s σ)
    → (↑s : ↑Shape) → C (↑s .↓shape) (↑s .symm)
  ↑Shape-uncurry f ↑⟨ ↓shape , symm ⟩ = f ↓shape symm

  isGroupoid-↑Shape : isGroupoid ↑Shape
  isGroupoid-↑Shape = recordIsOfHLevel 3 (isGroupoidΣ (isSet→isGroupoid Q.is-set-shape) λ ↓s → isGroupoid-↑Symm)

  ↑PosSet : ↑Shape → hSet ℓ
  ↑PosSet = ↑Shape-uncurry λ s → ↑SymmElim.rec s isGroupoidHSet
    (PosSet s)
    Q.PosPath
    Q.PosPathCompSquare

  ↑Pos : ↑Shape → Type ℓ
  ↑Pos = ⟨_⟩ ∘ ↑PosSet

  isSet-↑Pos : ∀ s → isSet (↑Pos s)
  isSet-↑Pos = str ∘ ↑PosSet

  ↑_ : GCont ℓ
  ↑ .GCont.Shape = ↑Shape
  ↑ .GCont.Pos = ↑Pos
  ↑ .GCont.is-groupoid-shape = isGroupoid-↑Shape
  ↑ .GCont.is-set-pos = isSet-↑Pos
