module GpdCont.QuotientContainer.Base where

open import GpdCont.Prelude
open import GpdCont.Univalence

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Logic using (hProp≡)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Subgroup

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
    symm-id : ∀ s → Symm (idEquiv (Pos s))
    symm-sym : ∀ {s t} (σ : Pos s ≃ Pos t) → Symm σ → Symm (invEquiv σ)
    symm-comp : ∀ {s t u} (σ : Pos s ≃ Pos t) (τ : Pos t ≃ Pos u)
      → Symm σ → Symm τ → Symm (σ ∙ₑ τ)

  PosΩGroup : Shape → Group ℓ
  PosΩGroup s = PosΩ s , grp-str where
    grp-str : GroupStr _
    grp-str .GroupStr.1g = idEquiv _
    grp-str .GroupStr._·_ = _∙ₑ_
    grp-str .GroupStr.inv = invEquiv
    grp-str .GroupStr.isGroup = makeIsGroup
      (isOfHLevel≃ 2 (is-set-pos _) (is-set-pos _)) -- equivalences are a set
      compEquiv-assoc -- composition is associative,
      compEquivEquivId compEquivIdEquiv -- unital,
      invEquiv-is-rinv invEquiv-is-linv -- and invertible

  isSet-∼ : ∀ {s t} → isSet (s ∼ t)
  isSet-∼ = isSetΣ (isOfHLevel≃ 2 (is-set-pos _) (is-set-pos _)) (isProp→isSet ∘ is-prop-symm)

  ∼-Path : ∀ {s t} {σ τ : s ∼ t} → σ .fst ≡ τ .fst → σ ≡ τ
  ∼-Path p i .fst = p i
  ∼-Path {σ} {τ} p i .snd = isProp→PathP (λ i → is-prop-symm (p i)) (σ .snd) (τ .snd) i

  isEquivSymm : isEquivRel _∼_
  isEquivSymm .isEquivRel.reflexive s = idEquiv _ , symm-id s
  isEquivSymm .isEquivRel.symmetric s t σ = invEquiv (σ .fst) , symm-sym (σ .fst) (σ .snd)
  isEquivSymm .isEquivRel.transitive s t u σ τ = σ .fst ∙ₑ τ .fst , symm-comp _ _ (σ .snd) (τ .snd)
  
  isTransSymm : isTrans _∼_
  isTransSymm = isEquivSymm .isEquivRel.transitive

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
    unfolding PosPath
    PosPathCompSquare : ∀ {s t u} → (σ : s ∼ t) (τ : t ∼ u) → Square (PosPath σ) (PosPath $ σ · τ) refl (PosPath τ)
    PosPathCompSquare σ τ = ΣSquareSet (λ X → isProp→isSet isPropIsSet) (uaCompEquivSquare (fst σ) (fst τ))

  SymmProp : ∀ {s} (p : Pos s ≃ Pos s) → hProp ℓ
  SymmProp p .fst = Symm p
  SymmProp p .snd = is-prop-symm p

  isSubGroupSymm : ∀ s → isSubgroup (PosΩGroup s) SymmProp
  isSubGroupSymm s .isSubgroup.id-closed = symm-id s
  isSubGroupSymm s .isSubgroup.op-closed = symm-comp _ _
  isSubGroupSymm s .isSubgroup.inv-closed = symm-sym _

  SymmSubGroup : ∀ s → Subgroup (PosΩGroup s)
  SymmSubGroup s .fst = SymmProp
  SymmSubGroup s .snd = isSubGroupSymm s

  SymmGroup : Shape → Group ℓ
  SymmGroup s = Subgroup→Group (PosΩGroup s) (SymmSubGroup s)

  SymmGroupStr : (s : Shape) → GroupStr (s ∼ s)
  SymmGroupStr = str ∘ SymmGroup

  Label : ∀ {ℓX} (X : Type ℓX) → Shape → Type _
  Label X s = Pos s → X
