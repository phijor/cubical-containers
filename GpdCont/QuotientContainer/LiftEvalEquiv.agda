module GpdCont.QuotientContainer.LiftEvalEquiv where

open import GpdCont.Prelude hiding (Lift)

open import GpdCont.QuotientContainer.Base using (QCont)
open import GpdCont.Univalence using (ua ; ua→)
open import GpdCont.SetTruncation using (setTruncateFstΣ≃)

import GpdCont.QuotientContainer.Lift as Lift
import GpdCont.QuotientContainer.Eval as QCEval
import GpdCont.Coffin.Eval as CoffinEval

open import Cubical.Foundations.Equiv renaming (invEquiv to _⁻ᵉ)
open import Cubical.Foundations.Equiv.Properties using (cong≃)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism as Isomorphism using (Iso ; isoToEquiv) renaming (invIso to _⁻ⁱ)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma.Properties as Sigma using (ΣPathP)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.SetQuotients as SQ using (_/_)

-- Each endo-map on hGroupoids can be truncated to one on hSets.
Tr : ∀ {ℓ} (F : hGroupoid ℓ → hGroupoid ℓ) → (hSet ℓ → hSet ℓ)
Tr F (X , is-set-X) .fst = ∥ ⟨ F (X , isSet→isGroupoid is-set-X) ⟩ ∥₂
Tr F (X , is-set-X) .snd = ST.isSetSetTrunc

isSetTr : ∀ {ℓ} (F : hGroupoid ℓ → hGroupoid ℓ) → ∀ X → isSet ⟨ Tr F X ⟩
isSetTr F X = str $ Tr F X

module EvalLiftLoop {ℓ} (Q : QCont ℓ) where
  import GpdCont.GroupoidContainer.Eval

  open module Q = QCont Q using (Shape ; Pos ; isSymm ; Symm ; PosSet)
  open module ⟦Q⟧ = QCEval Q using (_∼*_ ; ∼*→∼ ; ∼*→PathP*) renaming (⟦_⟧ to ⟦Q⟧ ; ⟦_⟧ᵗ to ⟦Q⟧ᵗ)

  open module ↑Q = Lift Q using (↑Shape ; ↑Pos ; ↑⟨_,_⟩ ; ↑Symm ; module ↑SymmElim) renaming (↑ to ↑Q)
  open module ⟦↑Q⟧ = CoffinEval ↑Q using () renaming (⟦_⟧ to ⟦↑Q⟧ ; ⟦_⟧ᵗ to ⟦↑Q⟧ᵗ ; ⟦-⟧ᵗ-Path to ⟦↑Q⟧ᵗ-Path)

  module LiftTruncEquiv (X : hSet ℓ) where
    opaque
      unfolding Q.PosPath ua CoffinEval.label
      to-lift-trunc : (⟦Q⟧ᵗ ⟨ X ⟩) → ⟨ Tr ⟦↑Q⟧ X ⟩
      to-lift-trunc = QCEval.⟦ Q ⟧ᵗ-rec (isSetTr ⟦↑Q⟧ X) [_]* [-]*-well-defined where
        [_]* : ∀ {s} (v : Pos s → ⟨ X ⟩) → ⟨ Tr ⟦↑Q⟧ X ⟩
        [ v ]* = ST.∣ CoffinEval.mk⟦ ↑Q ⟧ᵗ (↑Q.↑shape _ , v) ∣₂

        [-]*-well-defined : ∀ {s} (v w : Pos s → ⟨ X ⟩) → v ∼* w → [ v ]* ≡ [ w ]*
        [-]*-well-defined {s} v w r = cong ST.∣_∣₂ (⟦↑Q⟧ᵗ-Path shape-loop label-path) where
          shape-loop : ↑Q.↑shape s ≡ ↑Q.↑shape s
          shape-loop = ↑Q.↑loop (∼*→∼ r)

          label-path : PathP (λ i → ↑Q.↑Pos (shape-loop i) → ⟨ X ⟩) v w
          label-path = ∼*→PathP* r

      from-lift : CoffinEval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ → (⟦Q⟧ᵗ ⟨ X ⟩)
      from-lift = uncurry goal where
        isSetΠ⟦Q⟧ : ∀ ↑s → isSet ((↑Pos ↑s → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩)
        isSetΠ⟦Q⟧ ↑s = isSetΠ (λ ↑v → QCEval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩)

        [_]* : (s : Shape) → (v : Pos s → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩
        [ s ]* = QCEval.Label→⟦ Q ⟧ᵗ

        [_]*-loop : ∀ s → (σ : Symm s) → PathP (λ i → (ua (σ .fst) i → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩) [ s ]* [ s ]*
        [_]*-loop s σ = funExtDep λ { {x₀ = v} {x₁ = w} p → ⟦Q⟧.LabelEquiv→⟦_⟧Path v w (σ , p) }

        goal : (s : ↑Shape) → (v : ↑Pos s → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩
        goal = ↑Q.↑Shape-uncurry λ s → ↑SymmElim.elimSet s (λ σ → isSetΠ⟦Q⟧ ↑⟨ s , σ ⟩) [ s ]* [ s ]*-loop

    opaque
      unfolding from-lift
      from-lift-trunc : ⟨ Tr ⟦↑Q⟧ X ⟩ → (⟦Q⟧ᵗ ⟨ X ⟩)
      from-lift-trunc = ST.rec (QCEval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩) from-lift

    opaque
      unfolding ⟦↑Q⟧ from-lift-trunc to-lift-trunc
      lift-trunc-rightInv : ∀ (x : ⟨ Tr ⟦↑Q⟧ X ⟩) → to-lift-trunc (from-lift-trunc x) ≡ x
      lift-trunc-rightInv = ST.elim (isProp→isSet ∘ isPropPath) goal where
        isPropPath : ∀ x → isProp (to-lift-trunc (from-lift-trunc x) ≡ x)
        isPropPath x = ST.isSetSetTrunc _ x

        workhorse : (s : Shape) (v : Pos s → ⟨ X ⟩) → to-lift-trunc (from-lift-trunc ST.∣ ↑Q.↑shape s , v ∣₂) ≡ ST.∣ ↑Q.↑shape s , v ∣₂
        workhorse s v = refl

        lemma : ∀ (s : ↑Shape) (v : ↑Pos s → ⟨ X ⟩) → to-lift-trunc (from-lift-trunc ST.∣ (s , v) ∣₂) ≡ ST.∣ (s , v) ∣₂
        lemma = ↑Q.↑Shape-uncurry λ s → ↑SymmElim.elimProp s (λ σ → isPropΠ λ v → isPropPath ST.∣ ↑⟨ s , σ ⟩ , v ∣₂) (workhorse s)

        goal : ∀ (x : ⟦↑Q⟧ᵗ ⟨ X ⟩) → to-lift-trunc (from-lift-trunc ST.∣ x ∣₂) ≡ ST.∣ x ∣₂
        goal = uncurry lemma

    opaque
      unfolding from-lift-trunc to-lift-trunc
      lift-trunc-leftInv : ∀ (x : ⟦Q⟧ᵗ ⟨ X ⟩) → (from-lift-trunc (to-lift-trunc x)) ≡ x
      lift-trunc-leftInv = QCEval.⟦ Q ⟧ᵗ-elimProp {P = Motive} isPropMotive {! !} where
      -- lift-trunc-leftInv QCEval.mk⟦ s , v ⟧ᵗ = SQ.elimProp {P = Motive} isPropMotive [_]* v where
        Motive : ⟦Q⟧ᵗ ⟨ X ⟩ → Type ℓ
        Motive x = from-lift-trunc (to-lift-trunc x) ≡ x

        isPropMotive : ∀ x → isProp (Motive x)
        isPropMotive x = QCEval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩ _ _

        -- [_]* : ∀ {s} → (v : Pos s → ⟨ X ⟩) → Motive ?
        -- [ v ]* = refl

{-
    lift-trunc-Iso : Iso (⟦Q⟧ᵗ ⟨ X ⟩) ⟨ Tr ⟦↑Q⟧ X ⟩
    lift-trunc-Iso .Iso.fun = to-lift-trunc
    lift-trunc-Iso .Iso.inv = from-lift-trunc
    lift-trunc-Iso .Iso.rightInv = lift-trunc-rightInv
    lift-trunc-Iso .Iso.leftInv = lift-trunc-leftInv

  opaque
    unfolding CoffinEval.⟦_⟧
    evalLiftEquiv : ∀ X → ⟨ ⟦Q⟧ X ⟩ ≃ ⟨ Tr ⟦↑Q⟧ X ⟩
    evalLiftEquiv X =
      ⟦Q⟧ᵗ ⟨ X ⟩ ≃⟨ Isomorphism.isoToEquiv (LiftTruncEquiv.lift-trunc-Iso X) ⟩
      ∥ CoffinEval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ ∥₂ ≃∎

  evalLiftPath : ∀ X → ⟦Q⟧ X ≡ Tr ⟦↑Q⟧ X
  evalLiftPath X = TypeOfHLevel≡ 2 (ua $ evalLiftEquiv X)

module EvalLiftLoopEquational {ℓ} (Q : QCont ℓ) where
  open module Q = QCont Q using (Shape ; Pos ; Symm ; PosSet)
  open module ⟦Q⟧ = QCEval Q using (_∼*_ ; ∼*→∼ ; ∼*→PathP*) renaming (⟦_⟧ to ⟦Q⟧ ; ⟦_⟧ᵗ to ⟦Q⟧ᵗ)

  open module ↑Q = Lift Q using (↑Shape ; ↑Pos ; ↑⟨_,_⟩ ; ↑Symm ; module ↑SymmElim) renaming (↑ to ↑Q)
  open module ⟦↑Q⟧ = CoffinEval ↑Q using () renaming (⟦_⟧ to ⟦↑Q⟧ ; ⟦_⟧ᵗ to ⟦↑Q⟧ᵗ ; ⟦-⟧ᵗ-Path to ⟦↑Q⟧ᵗ-Path)

  module PosEquiv (X : Type ℓ) (s : Shape) where
    opaque
      unfolding Q.PosPath ua
      PosIso : Iso ∥ Σ[ σ ∈ ↑Symm s ] (↑Pos ↑⟨ s , σ ⟩ → X) ∥₂ ((Pos s → X) / _∼*_)
      PosIso = record { the-iso } where module the-iso where
        fun : _
        fun = ST.rec SQ.squash/ $ uncurry
          $ ↑SymmElim.elimSet s
            (λ σ → isSetΠ λ v → SQ.squash/)
            SQ.[_]
            (λ σ → funExtDep λ {x₀ = v} {x₁ = w} vσ≡w → SQ.eq/ v w (σ , vσ≡w))

        inv : _
        inv = SQ.rec ST.isSetSetTrunc
          (λ v → ST.∣ ↑Symm.⋆ , v ∣₂)
          λ v w σ → cong ST.∣_∣₂ (ΣPathP (↑Symm.loop (∼*→∼ σ) , ∼*→PathP* σ))

        leftInv : _
        leftInv = ST.elim (λ ∣v∣ → isProp→isSet (ST.isSetSetTrunc _ ∣v∣))
          $ uncurry (↑SymmElim.elimProp s (λ (σ : ↑Symm s) → isPropΠ λ v → ST.isSetSetTrunc _ ST.∣ σ , v ∣₂) λ _ → refl)

        rightInv : _
        rightInv = SQ.elimProp (λ v/∼ → SQ.squash/ _ v/∼) λ _ → refl

    PosEquiv :  ∥ Σ[ σ ∈ ↑Symm s ] (↑Pos ↑⟨ s , σ ⟩ → X) ∥₂ ≃ ((Pos s → X) / _∼*_)
    PosEquiv = isoToEquiv PosIso

  opaque
    unfolding ⟦↑Q⟧
    thm : ∀ X → ⟨ Tr ⟦↑Q⟧ X ⟩ ≃ ⟨ ⟦Q⟧ X ⟩
    thm X =
      ∥ ⟦↑Q⟧ᵗ ⟨ X ⟩ ∥₂ ≃⟨⟩
      ∥ Σ[ ↑s ∈ ↑Shape ] (↑Pos (↑s) → ⟨ X ⟩) ∥₂                       ≃⟨ cong≃ ∥_∥₂ Sigma.Σ-assoc-≃ ⟩
      ∥ Σ[ s ∈ Shape ] Σ[ v ∈ ↑Symm s ] (↑Pos ↑⟨ s , v ⟩ → ⟨ X ⟩) ∥₂  ≃⟨ setTruncateFstΣ≃ Q.is-set-shape ⟩
      Σ[ s ∈ Shape ] ∥ Σ[ v ∈ ↑Symm s ] (↑Pos ↑⟨ s , v ⟩ → ⟨ X ⟩) ∥₂  ≃⟨ Sigma.Σ-cong-equiv-snd $ PosEquiv.PosEquiv ⟨ X ⟩ ⟩
      Σ[ s ∈ Shape ] (Pos s → ⟨ X ⟩) / _∼*_                           ≃⟨ (⟦Q⟧ᵗ ⟨ X ⟩ ≃Σ) ⁻ᵉ ⟩
      ⟨ ⟦Q⟧ X ⟩                                                       ≃∎
      -}
