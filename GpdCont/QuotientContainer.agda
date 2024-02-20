module GpdCont.QuotientContainer where

open import GpdCont.Prelude
open import GpdCont.Univalence using (ua ; uaCompEquivSquare)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)

open BinaryRelation using (isEquivRel ; isTrans ; isSym)

record QCont (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Shape : Type ℓ
    Pos : Shape → Type ℓ

    -- TODO: Should this be homogeneous or heterogeneous?
    Symm : ∀ {s t} → Pos s ≃ Pos t → Type ℓ

  PosΩ : (s : Shape) → Type ℓ
  PosΩ s = Pos s ≃ Pos s

  _∼_ : (s t : Shape) → Type ℓ
  s ∼ t = Σ[ p ∈ Pos s ≃ Pos t ] Symm p

  field
    is-set-shape : isSet Shape
    is-set-pos : ∀ s → isSet (Pos s)
    is-prop-symm : ∀ {s t} (p : Pos s ≃ Pos t) → isProp (Symm p)
    symm-comp : ∀ {s t u} (σ : Pos s ≃ Pos t) (τ : Pos t ≃ Pos u)
      → Symm σ → Symm τ → Symm (σ ∙ₑ τ)


  opaque
    isEquivSymm : isEquivRel _∼_
    isEquivSymm = {! !}
  
  opaque
    isTransSymm : isTrans _∼_
    isTransSymm s t u (σ , σ-symm) (τ , τ-symm) = σ ∙ₑ τ , symm-comp σ τ σ-symm τ-symm

    _·_ : ∀ {s t u} → (s ∼ t) → (t ∼ u) → (s ∼ u)
    _·_ {s} {t} {u} = isTransSymm s t u

  opaque
    isSymSymm : isSym _∼_
    isSymSymm = isEquivSymm .isEquivRel.symmetric

    _∼⁻¹ : ∀ {s t} → s ∼ t → t ∼ s
    _∼⁻¹ = isSymSymm _ _

  opaque
    ShapeSet : hSet ℓ
    ShapeSet .fst = Shape
    ShapeSet .snd = is-set-shape

  opaque
    PosSet : Shape → hSet ℓ
    PosSet s .fst = Pos s
    PosSet s .snd = is-set-pos s

    PosPath : ∀ {s t} (σ : s ∼ t) → PosSet s ≡ PosSet t
    PosPath = TypeOfHLevel≡ 2 ∘ ua ∘ fst

  opaque
    unfolding _·_ PosPath
    PosPathCompSquare : ∀ {s t u} → (σ : s ∼ t) (τ : t ∼ u) → Square (PosPath σ) (PosPath $ σ · τ) refl (PosPath τ)
    PosPathCompSquare σ τ = ΣSquareSet (λ X → isProp→isSet isPropIsSet) (uaCompEquivSquare (fst σ) (fst τ))

  opaque
    SymmProp : ∀ {s} (p : Pos s ≃ Pos s) → hProp ℓ
    SymmProp p .fst = Symm p
    SymmProp p .snd = is-prop-symm p

module Eval {ℓ} (Q : QCont ℓ) where
  open QCont Q
  opaque
    LabelEquiv : (s : Shape) (X : Type ℓ) → (v w : Pos s → X) → Type ℓ
    LabelEquiv s X v w = Σ[ p ∈ PosΩ s ] Symm p × PathP (λ i → ua p i → X) v w

    _∼*_ : ∀ {s} {X : Type ℓ} → (v w : Pos s → X) → Type ℓ
    _∼*_ {s} {X} = LabelEquiv s X

    _∼*⁻¹ : ∀ {s} {X : Type ℓ} {v w : Pos s → X} → v ∼* w → w ∼* v
    _∼*⁻¹ = {! !}

    ∼*→∼ : ∀ {X} {s} {v w : Pos s → X} → v ∼* w → s ∼ s
    ∼*→∼ (σ , (is-symm-σ , _)) = σ , is-symm-σ

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
