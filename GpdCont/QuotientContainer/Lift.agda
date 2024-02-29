open import GpdCont.QuotientContainer.Base as QC using (QCont)

module GpdCont.QuotientContainer.Lift {ℓ} (Q : QCont ℓ) where

open import GpdCont.Prelude hiding (Lift)
open import GpdCont.GroupoidContainer.Base as GC using (GCont)
open import GpdCont.Univalence as UA using (ua→ ; pathToEquiv ; ua)
open import GpdCont.Groupoid using (isSkeletal)
open import GpdCont.SetTruncation

import GpdCont.Delooping

open import Cubical.Data.Sigma.Properties as Sigma using ()
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (cong≃)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (isProp→SquareP ; flipSquare)
open import Cubical.HITs.GroupoidQuotients as GQ using (_//_)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.Functions.Embedding

open QCont Q using (Shape ; Pos ; Symm ; _∼_ ; PosSet)

open module Q = QCont Q using (_·_)

open import Cubical.HITs.SetQuotients as SQ using (_/_)

module ↑SymmElim (s : Shape) =
  GpdCont.Delooping (s ∼ s) _·_
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

opaque
  ↑ShapeTrunc≃Shape : ∥ ↑Shape ∥₂ ≃ Shape
  ↑ShapeTrunc≃Shape =
    ∥ ↑Shape ∥₂                 ≃⟨ cong≃ ∥_∥₂ (↑Shape ≃Σ) ⟩
    ∥ ↑Shape asΣ ∥₂             ≃⟨ setTruncateFstΣ≃ Q.is-set-shape ⟩
    Σ[ s ∈ Shape ] ∥ ↑Symm s ∥₂ ≃⟨ Sigma.Σ-contractSnd ↑SymmElim.isConnectedDelooping ⟩
    Shape ≃∎

  Component : ∥ ↑Shape ∥₂ → Type ℓ
  Component = ↑Symm ∘ equivFun ↑ShapeTrunc≃Shape

  ↑Shape≃TotalTrunc : ↑Shape ≃ Σ ∥ ↑Shape ∥₂ Component
  ↑Shape≃TotalTrunc =
    ↑Shape                  ≃⟨ ↑Shape ≃Σ ⟩
    Σ Shape ↑Symm           ≃⟨ invEquiv (Sigma.Σ-cong-equiv-fst {B = ↑Symm} ↑ShapeTrunc≃Shape) ⟩
    Σ ∥ ↑Shape ∥₂ Component ≃∎


  isSkeletal-↑Shape : isSkeletal ↑Shape
  isSkeletal-↑Shape = sk where
    sk : isSkeletal ↑Shape
    sk .isSkeletal.Component = Component
    sk .isSkeletal.group-str-component = ↑SymmElim.deloopingGroupStr ∘ equivFun ↑ShapeTrunc≃Shape
    sk .isSkeletal.total-path = ua ↑Shape≃TotalTrunc


↑PosSet : ↑Shape → hSet ℓ
↑PosSet = ↑Shape-uncurry λ s → ↑SymmElim.rec s isGroupoidHSet
  (PosSet s)
  Q.PosPath
  Q.PosPathCompSquare

↑Pos : ↑Shape → Type ℓ
↑Pos = ⟨_⟩ ∘ ↑PosSet

isSet-↑Pos : ∀ s → isSet (↑Pos s)
isSet-↑Pos = str ∘ ↑PosSet

↑ : GCont ℓ
↑ .GCont.Shape = ↑Shape
↑ .GCont.Pos = ↑Pos
↑ .GCont.is-groupoid-shape = isGroupoid-↑Shape
↑ .GCont.is-set-pos = isSet-↑Pos
