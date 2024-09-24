module GpdCont.QuotientContainer.Base where

open import GpdCont.Prelude hiding (_▷_ ; _◁_)
open import GpdCont.Univalence

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Functions.Logic using (hProp≡)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Subgroup

open BinaryRelation using (isEquivRel ; isTrans ; isSym)

record QCont (ℓ : Level) : Type (ℓ-suc ℓ) where
  no-eta-equality
  field
    Shape : Type ℓ
    Pos : Shape → Type ℓ
    isSymm : ∀ {s} → Pos s ≃ Pos s → Type ℓ

  PosΩ : (s : Shape) → Type ℓ
  PosΩ s = Pos s ≃ Pos s

  Symm : (s : Shape) → Type ℓ
  Symm s = Σ[ p ∈ Pos s ≃ Pos s ] isSymm p

  field
    is-set-shape : isSet Shape
    is-set-pos : ∀ s → isSet (Pos s)
    is-prop-symm : ∀ {s} (p : Pos s ≃ Pos s) → isProp (isSymm p)
    symm-id : ∀ s → isSymm (idEquiv (Pos s))
    symm-sym : ∀ {s} (σ : Pos s ≃ Pos s) → isSymm σ → isSymm (invEquiv σ)
    symm-comp : ∀ {s} (σ τ : Pos s ≃ Pos s)
      → isSymm σ → isSymm τ → isSymm (σ ∙ₑ τ)

  _⁺ : ∀ {s} → Symm s → Pos s → Pos s
  (σ , _) ⁺ = equivFun σ

  _⁻ : ∀ {s} → Symm s → Pos s → Pos s
  (σ , _) ⁻ = invEq σ

  Eq⁺ : ∀ {s} {σ τ : Symm s} → σ ⁺ ≡ τ ⁺ → σ ≡ τ
  Eq⁺ p = Σ≡Prop is-prop-symm (equivEq p)

  infixr 9 _▷_ _◁_
  _▷_ : ∀ {ℓ'} {A : Type ℓ'} {s : Shape} → (f : A → Pos s) (σ : Symm s) → A → Pos s
  _▷_ f σ = σ ⁺ ∘ f

  _◁_ : ∀ {ℓ'} {B : Type ℓ'} {s : Shape} → (σ : Symm s) (f : Pos s → B) → Pos s → B
  σ ◁ f = f ∘ σ ⁺

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

  isSetSymm : ∀ {s} → isSet $ Symm s
  isSetSymm = isSetΣ (isOfHLevel≃ 2 (is-set-pos _) (is-set-pos _)) (isProp→isSet ∘ is-prop-symm)

  SymmPath : ∀ {s} {σ τ : Symm s} → σ .fst ≡ τ .fst → σ ≡ τ
  SymmPath p i .fst = p i
  SymmPath {σ} {τ} p i .snd = isProp→PathP (λ i → is-prop-symm (p i)) (σ .snd) (τ .snd) i

  -- isEquivSymm : isEquivRel Symm
  -- isEquivSymm .isEquivRel.reflexive s = idEquiv _ , symm-id s
  -- isEquivSymm .isEquivRel.symmetric s t σ = invEquiv (σ .fst) , symm-sym (σ .fst) (σ .snd)
  -- isEquivSymm .isEquivRel.transitive s t u σ τ = σ .fst ∙ₑ τ .fst , symm-comp _ _ (σ .snd) (τ .snd)
  
  -- isTransSymm : isTrans _∼_
  -- isTransSymm = isEquivSymm .isEquivRel.transitive

  infixl 15 _·_
  _·_ : ∀ {s} → Symm s → Symm s → Symm s
  _·_ {s} (σ , is-symm-σ) (τ , is-symm-τ) = σ ∙ₑ τ , symm-comp _ _ is-symm-σ is-symm-τ

  -- opaque
  --   isSymSymm : isSym _∼_
  --   isSymSymm = isEquivSymm .isEquivRel.symmetric

  --   _∼⁻¹ : ∀ {s t} → s ∼ t → t ∼ s
  --   _∼⁻¹ = isSymSymm _ _

  opaque
    ShapeSet : hSet ℓ
    ShapeSet .fst = Shape
    ShapeSet .snd = is-set-shape

  PosSet : Shape → hSet ℓ
  PosSet s .fst = Pos s
  PosSet s .snd = is-set-pos s

  opaque
    PosPath : ∀ {s} (σ : Symm s) → PosSet s ≡ PosSet s
    PosPath = TypeOfHLevel≡ 2 ∘ ua ∘ fst

  opaque
    unfolding PosPath
    PosPathCompSquare : ∀ {s} → (σ τ : Symm s) → Square (PosPath σ) (PosPath $ σ · τ) refl (PosPath τ)
    PosPathCompSquare σ τ = ΣSquareSet (λ X → isProp→isSet isPropIsSet) (uaCompEquivSquare (fst σ) (fst τ))

  SymmProp : ∀ {s} (p : Pos s ≃ Pos s) → hProp ℓ
  SymmProp p .fst = isSymm p
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

  SymmGroupStr : (s : Shape) → GroupStr (Symm s)
  SymmGroupStr = str ∘ SymmGroup

  module SymmGroup (s : Shape) = GroupStr (SymmGroupStr s)

  _⁻¹ : ∀ {s} → Symm s → Symm s
  _⁻¹ {s} = SymmGroup.inv s

  id-symm : ∀ {s} → Symm s
  id-symm {s} = SymmGroup.1g s

  Label : ∀ {ℓX} (X : Type ℓX) → Shape → Type _
  Label X s = Pos s → X
