module GpdCont.QuotientContainer.Examples where

open import GpdCont.Prelude
open import GpdCont.Univalence using (ua ; ua→ ; ua→⁻ ; ua→⁻ExtEquiv)
open import GpdCont.QuotientContainer.Base
open import GpdCont.QuotientContainer.Premorphism
open import GpdCont.QuotientContainer.Morphism
open import GpdCont.QuotientContainer.Category
open import GpdCont.QuotientContainer.Eval as Eval using (⟦_⟧)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.Extend using (extend₂)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (substIso)
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv)
open import Cubical.Functions.Involution using (isInvolution ; involEquiv)
open import Cubical.Relation.Nullary.Base
open import Cubical.Data.Unit
open import Cubical.Data.Bool as Bool hiding (_⊕_)
open import Cubical.Data.SumFin
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using () renaming (rec to ex-falso)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms using (GroupIso ; IsGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (GroupIso→GroupEquiv)
open import Cubical.Algebra.Group.GroupPath using (GroupPath)
open import Cubical.Categories.Category using (isUnivalent ; CatIso ; isPropIsIso ; pathToIso)

open QCont hiding (_⁻¹ ; _·_)
open Premorphism
open Morphism

AllSymmetries : ∀ {ℓ} (S : hSet ℓ) (P : ⟨ S ⟩ → hSet ℓ) → QCont ℓ
AllSymmetries S P .Shape = ⟨ S ⟩
AllSymmetries S P .Pos = ⟨_⟩ ∘ P
AllSymmetries S P .isSymm = const Unit*
AllSymmetries S P .is-set-shape = str S
AllSymmetries S P .is-set-pos = str ∘ P
AllSymmetries S P .is-prop-symm = const isPropUnit*
AllSymmetries S P .symm-id = λ _ → tt*
AllSymmetries S P .symm-sym = λ σ _ → tt*
AllSymmetries S P .symm-comp = λ σ τ _ _ → tt*

UnorderedTuple : (n : ℕ) → QCont ℓ-zero
UnorderedTuple n = AllSymmetries (Unit , isSetUnit) (const (Fin n , isSetFin))

_∼permute_ : ∀ {ℓ} {n} {X : Type ℓ} (v w : Fin n → X) → Type ℓ
_∼permute_ {n} v w = ∃[ σ ∈ Fin n ≃ Fin n ] v ≡ w ∘ equivFun σ

UnorderedTupleExt : ∀ n X → ⟨ ⟦ UnorderedTuple n ⟧ X ⟩ ≃ (Fin n → ⟨ X ⟩) / _∼permute_
UnorderedTupleExt n X =
  ⟨ ⟦ UnorderedTuple n ⟧ X ⟩ ≃⟨ _ ≃Σ ⟩
  Σ[ _ ∈ Unit ] ((Fin n → ⟨ X ⟩) / LabelEquiv _ ⟨ X ⟩) ≃⟨ Σ-contractFst isContrUnit ⟩
  (Fin n → ⟨ X ⟩) / LabelEquiv tt ⟨ X ⟩ ≃⟨ relEquiv→QuotIdEquiv LabelEquiv≃Permute ⟩
  (Fin n → ⟨ X ⟩) / _∼permute_ ≃∎
  where

  open import GpdCont.SetQuotients using (relEquiv→QuotIdEquiv)
  open Eval (UnorderedTuple n) hiding (⟦_⟧)
  module _ {v w : Fin n → ⟨ X ⟩} where
    LabelEquiv≃Permute : LabelEquiv tt ⟨ X ⟩ v w ≃ v ∼permute w
    LabelEquiv≃Permute = PT.propTrunc≃ (Σ-cong-equiv symm-equiv label-equiv) where
      symm-equiv : Symm (UnorderedTuple n) tt ≃ (Fin n ≃ Fin n)
      symm-equiv = Σ-contractSnd λ _ → isContrUnit*

      label-equiv : ((g , _) : Symm (UnorderedTuple n) tt) → (PathP (λ i → ua g i → ⟨ X ⟩) v w) ≃ (v ≡ w ∘ equivFun g)
      label-equiv (g , _) = ua→⁻ExtEquiv

Id : QCont ℓ-zero
Id = UnorderedTuple 1

UPair : QCont ℓ-zero
UPair = UnorderedTuple 2

private
  swap-two : Fin 2 → Fin 2
  swap-two fzero = fsuc fzero
  swap-two (fsuc fzero) = fzero

  invol-swap-two : isInvolution swap-two
  invol-swap-two fzero = refl
  invol-swap-two (fsuc fzero) = refl

  swap-≃ : Fin 2 ≃ Fin 2
  swap-≃ = involEquiv {f = swap-two} invol-swap-two

degenDup : Premorphism Id UPair (id _)
degenDup .pos-mor _ = const fzero
degenDup .symm-pres _ g = ∃-intro (φ g) isNaturalFiller-φ where
  φ : Symm Id _ → Symm UPair _
  φ = const (swap-≃ , _)

  isNaturalFiller-φ : isNaturalFiller Id UPair (id _) (λ _ _ → fzero) g (φ g)
  isNaturalFiller-φ = isProp→ (isContr→isProp isContrSumFin1) _ _
