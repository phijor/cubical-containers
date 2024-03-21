{-# OPTIONS --lossy-unification #-}

open import GpdCont.QuotientContainer.Base as QC using (QCont)

module GpdCont.QuotientContainer.Lift {ℓ} (Q : QCont ℓ) where

open import GpdCont.Prelude hiding (Lift)
open import GpdCont.Coffin.Base using (Coffin)
open import GpdCont.Skeleton using (Skeleton)
open import GpdCont.GroupAction using (_-Set)

import GpdCont.Delooping

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import GpdCont.SetTruncation using (setTruncateFstΣ≃)
import Cubical.Data.Sigma.Properties as Sigma

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

isGroupoid-↑Shape : isGroupoid ↑Shape
isGroupoid-↑Shape = isGroupoidΣ (isSet→isGroupoid Q.is-set-shape) λ s → ↑SymmElim.isGroupoid𝔹

↑ShapeGroupoid : hGroupoid ℓ
↑ShapeGroupoid .fst = ↑Shape
↑ShapeGroupoid .snd = isGroupoid-↑Shape

Trunc-↑Shape-equiv : ∥ ↑Shape ∥₂ ≃ Shape
Trunc-↑Shape-equiv = setTruncateFstΣ≃ Q.is-set-shape ∙ₑ Sigma.Σ-contractSnd ↑SymmElim.isConnectedDelooping

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

↑Shape-uncurry : ∀ {ℓC} {C : (s : Shape) → ↑Symm s → Type ℓC}
  → (f : ∀ s σ → C s σ)
  → (↑s : ↑Shape) → C (↑s .↓shape) (↑s .symm)
↑Shape-uncurry f ↑⟨ ↓shape , symm ⟩ = f ↓shape symm

↑Shape-curry : ∀ {ℓC} {C : ↑Shape → Type ℓC}
  → (f : ∀ s → C s)
  → (s : Shape) (σ : ↑Symm s) → C ↑⟨ s , σ ⟩
↑Shape-curry f s σ = f ↑⟨ s , σ ⟩

↑shape-trunc : ∥ ↑Shape ∥₂ → ↑Shape
↑shape-trunc = ↑shape ∘ equivFun Trunc-↑Shape-equiv

↑ShapeSkeleton : Skeleton ↑ShapeGroupoid
↑ShapeSkeleton .Skeleton.component-section x = sec where
  sec : fiber ST.∣_∣₂ x
  sec .fst = ↑shape-trunc x
  sec .snd = ST.elim {B = λ x → ST.∣ ↑shape-trunc x ∣₂ ≡ x} (λ _ → ST.isSetPathImplicit) (↑Shape-uncurry λ s → ↑SymmElim.elimProp s (λ _ → ST.isSetSetTrunc _ _) refl) x

↑PosSet : ↑Shape → hSet ℓ
↑PosSet = ↑Shape-uncurry λ s → ↑SymmElim.rec s isGroupoidHSet
  (PosSet s)
  Q.PosPath
  Q.PosPathCompSquare

↑Pos : ↑Shape → Type ℓ
↑Pos = ⟨_⟩ ∘ ↑PosSet

isSet-↑Pos : ∀ s → isSet (↑Pos s)
isSet-↑Pos = str ∘ ↑PosSet

↑PosAction : ∀ (s : ∥ ↑Shape ∥₂) → Skeleton.ComponentGroup ↑ShapeSkeleton s -Set
↑PosAction _ ._-Set.action σ = ↑PosSet (σ .↓shape)

↑ : Coffin ℓ
↑ .Coffin.Shape = ↑Shape
↑ .Coffin.is-groupoid-shape = isGroupoid-↑Shape
↑ .Coffin.shape-skeleton = ↑ShapeSkeleton
↑ .Coffin.componentGroupSet = ↑PosAction
