open import GpdCont.QuotientContainer.Base as QC using (QCont)

module GpdCont.QuotientContainer.Lift {ℓ} (Q : QCont ℓ) where

open import GpdCont.Prelude hiding (Lift)
open import GpdCont.Coffin.Base using (Coffin)
open import GpdCont.Univalence as UA using (ua→ ; pathToEquiv ; ua)
open import GpdCont.Group using (Group)
open import GpdCont.Groupoid using (Skeleton)
open import GpdCont.GroupAction using (_-Set)
open import GpdCont.SetTruncation

import GpdCont.Delooping

open import Cubical.Data.Sigma.Properties as Sigma using ()
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (cong≃)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (isProp→SquareP ; flipSquare)
open import Cubical.HITs.GroupoidQuotients as GQ using (_//_)
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.Functions.Embedding

private
  open QCont Q using (Shape ; Pos ; Symm ; _∼_ ; PosSet)

  open module Q = QCont Q using (_·_)

module ↑SymmElim (s : Shape) =
  GpdCont.Delooping (s ∼ s) _·_
    renaming (𝔹 to ↑Symm)

open ↑SymmElim
  using (↑Symm)
  public

↑Shape : Type ℓ
↑Shape = Σ Shape ↑Symm

-- record ↑Shape : Type ℓ where
--   constructor ↑⟨_,_⟩
--   field
--     ↓shape : Shape
--     symm : ↑Symm ↓shape

open Σ public renaming (fst to ↓shape ; snd to symm)

pattern ↑⟨_,_⟩ ↓shape symm = ↓shape , symm

↑shape : (s : Shape) → ↑Shape
↑shape s .↓shape = s
↑shape s .symm = ↑Symm.⋆

↑loop : ∀ {s : Shape} → s ∼ s → ↑shape s ≡ ↑shape s
↑loop r i .↓shape = _
↑loop r i .symm = ↑Symm.loop r i

↑loop-comp : ∀ {s} → (g h : s ∼ s) → compSquareFiller (↑loop g) (↑loop h) (↑loop (g · h))
↑loop-comp g h i j .↓shape = _
↑loop-comp g h i j .symm = ↑Symm.loop-comp g h i j

-- unquoteDecl ↑ShapeIsoΣ = declareRecordIsoΣ ↑ShapeIsoΣ (quote ↑Shape)

-- instance
--   ↑ShapeToΣ : RecordToΣ ↑Shape
--   ↑ShapeToΣ = toΣ ↑ShapeIsoΣ

↑Shape-uncurry : ∀ {ℓC} {C : (s : Shape) → ↑Symm s → Type ℓC}
  → (f : ∀ s σ → C s σ)
  → (↑s : ↑Shape) → C (↑s .↓shape) (↑s .symm)
↑Shape-uncurry f ↑⟨ ↓shape , symm ⟩ = f ↓shape symm

↑Shape-curry : ∀ {ℓC} {C : ↑Shape → Type ℓC}
  → (f : ∀ s → C s)
  → (s : Shape) (σ : ↑Symm s) → C ↑⟨ s , σ ⟩
↑Shape-curry f s σ = f ↑⟨ s , σ ⟩

↑ShapeSkeleton : Skeleton ℓ
↑ShapeSkeleton .Skeleton.Index = Shape
↑ShapeSkeleton .Skeleton.Component = ↑Symm
↑ShapeSkeleton .Skeleton.is-set-index = Q.is-set-shape
↑ShapeSkeleton .Skeleton.group-str-component = ↑SymmElim.deloopingGroupStr

↑PosSet : ↑Shape → hSet ℓ
↑PosSet = ↑Shape-uncurry λ s → ↑SymmElim.rec s isGroupoidHSet
  (PosSet s)
  Q.PosPath
  Q.PosPathCompSquare

↑Pos : ↑Shape → Type ℓ
↑Pos = ⟨_⟩ ∘ ↑PosSet

isSet-↑Pos : ∀ s → isSet (↑Pos s)
isSet-↑Pos = str ∘ ↑PosSet

↑PosAction : ∀ s → Skeleton.ComponentGroup ↑ShapeSkeleton s -Set
↑PosAction s ._-Set.action σ = ↑PosSet ↑⟨ s , σ ⟩

↑ : Coffin ℓ
↑ .Coffin.shape-skeleton = ↑ShapeSkeleton
↑ .Coffin.PosSet = ↑PosAction
