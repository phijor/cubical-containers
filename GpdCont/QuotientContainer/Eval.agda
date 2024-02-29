open import GpdCont.QuotientContainer.Base

module GpdCont.QuotientContainer.Eval {ℓ} (Q : QCont ℓ) where

open import GpdCont.Prelude
open import GpdCont.Univalence

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)

open BinaryRelation using (isEquivRel ; isTrans ; isSym)

open QCont Q
opaque
  unfolding _·_ ua PosPath PosPathCompSquare
  LabelEquiv : (s : Shape) (X : Type ℓ) → (v w : Pos s → X) → Type ℓ
  LabelEquiv s X v w = Σ[ σ ∈ s ∼ s ] PathP (λ i → ua (σ .fst) i → X) v w

  _∼*_ : ∀ {s} {X : Type ℓ} → (v w : Pos s → X) → Type ℓ
  _∼*_ {s} {X} = LabelEquiv s X

  isTrans-∼* : ∀ {s} {X : Type ℓ} → isTrans (_∼*_ {s} {X})
  isTrans-∼* v w u σ* τ* .fst = σ* .fst · τ* .fst
  isTrans-∼* {s} {X} v w u σ* τ* .snd = λ i → comp (λ j → comp-equiv-square j i → X) (system i) {! (v ∘ ua-unglue σ i) !} where
    σ τ σ∙τ : Pos s ≃ Pos s
    σ = σ* .fst .fst
    τ = τ* .fst .fst
    σ∙τ = σ ∙ₑ τ
    comp-equiv-square : compSquareFiller (ua σ) (ua τ) (ua σ∙τ)
    comp-equiv-square = uaCompEquivSquare (σ* .fst .fst) (τ* .fst .fst)

    system : (i j : I) → Partial (i ∨ ~ i) (comp-equiv-square j i → X)
    system i j (i = i0) = λ s → {! !}
    system i j (i = i1) = {!ua-unglue (σ∙τ) !}

  ∼*→PosEquiv : ∀ {X} {s} {v w : Pos s → X} → v ∼* w → Pos s ≃ Pos s
  ∼*→PosEquiv ((σ , is-symm-σ) , _) = σ

  ∼*→∼ : ∀ {X} {s} {v w : Pos s → X} → v ∼* w → s ∼ s
  ∼*→∼ ((σ , is-symm-σ) , _) = σ , is-symm-σ

  ∼*→PathP* : ∀ {X} {s} {v w : Pos s → X} → (σ : v ∼* w) → PathP (λ i → ua (∼*→PosEquiv σ) i → X) v w
  ∼*→PathP* ((_ , _) , p) = p

opaque
  ⟦_⟧ᵗ : Type ℓ → Type ℓ
  ⟦_⟧ᵗ X = Σ[ s ∈ Shape ] (Pos s → X) / _∼*_

  mk⟦_⟧ᵗ : ∀ {X} → Σ[ s ∈ Shape ] ((Pos s → X) / _∼*_) → ⟦_⟧ᵗ X
  mk⟦_⟧ᵗ x = x

  Label→⟦_⟧ᵗ : ∀ {X} {s : Shape} → (v : Pos s → X) → ⟦_⟧ᵗ X
  Label→⟦_⟧ᵗ {s} v = (s , SQ.[ v ])

  isSet-⟦_⟧ᵗ : ∀ X → isSet (⟦_⟧ᵗ X)
  isSet-⟦_⟧ᵗ X = isSetΣ is-set-shape λ s → SQ.squash/

  ⟦_⟧′ : Type ℓ → hSet ℓ
  ⟦_⟧′ X .fst = ⟦_⟧ᵗ X
  ⟦_⟧′ X .snd = isSet-⟦_⟧ᵗ X

  ⟦_⟧ : hSet ℓ → hSet ℓ
  ⟦_⟧ X = ⟦_⟧′ ⟨ X ⟩
