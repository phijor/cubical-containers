module GpdCont.Axioms.TruncatedChoice where

open import GpdCont.Prelude
open import GpdCont.Fibration
open import GpdCont.PropositionalTruncation using (propTruncIso)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism as Isomorphism using (Iso ; section ; invIso ; isoToEquiv)
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.Truncation as Tr using (∥_∥_)

private
  variable
    ℓ ℓX ℓY : Level
    X Y : Type ℓ

-- A family of n-types has m-choice iff
--  "the family is pointwise m-inhabited"
-- implies
--  "the family has an m-truncated section"
hasChoice : (n m : HLevel) (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ n) → Type _
hasChoice n m X Y = ((x : ⟨ X ⟩) → ∥ ⟨ Y x ⟩ ∥ m) → ∥ ((x : ⟨ X ⟩) → ⟨ Y x ⟩) ∥ m

isOfHLevelHasChoice : ∀ {n} (m : HLevel) (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ n) → isOfHLevel m (hasChoice n m X Y)
isOfHLevelHasChoice m _ _ = isOfHLevelΠ m λ _ → Tr.isOfHLevelTrunc m

-- The (n,m) axiom of choice says that all families of n-types
-- have m-truncated sections whenever they are pointwise m-inhabited.
AC : (ℓ : Level) (n m : HLevel) → Type _
AC ℓ n m = ∀ (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ n) → hasChoice n m X Y

-- In the special case of (n = 2, m = 1), we recover the content of the usual
-- axiom of choice for sets: A family of sets has choice if being pointwise
-- merely inhabited implies merely having a global section.
hasSetChoice : (X : hSet ℓX) (Y : ⟨ X ⟩ → hSet ℓY) → Type _
hasSetChoice X Y = ((x : ⟨ X ⟩) → ∥ ⟨ Y x ⟩ ∥₁) → ∥ ((x : ⟨ X ⟩) → ⟨ Y x ⟩) ∥₁

-- The axiom of (set-) choice: All merely inhabited families merely have sections.
ASC : (ℓX ℓY : Level) → Type _
ASC ℓX ℓY = ∀ (X : hSet ℓX) (Y : ⟨ X ⟩ → hSet ℓY) → hasSetChoice X Y

isPropHasChoice : (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) → isProp (hasSetChoice X Y)
isPropHasChoice _ _ = isPropΠ λ _ → PT.isPropPropTrunc

hasSetChoice≃hasChoice[2,1] : ∀ (X : hSet ℓ) Y → hasSetChoice X Y ≃ hasChoice 2 1 X Y
hasSetChoice≃hasChoice[2,1] X Y = equiv→ (equivΠCod λ x → Tr.propTrunc≃Trunc1) Tr.propTrunc≃Trunc1

-- A functions is split if it merely has a section.
isSplit : (f : X → Y) → Type _
isSplit {X} {Y} f = ∃[ g ∈ (Y → X) ] section f g

isPropIsSplit : (f : X → Y) → isProp (isSplit f)
isPropIsSplit f = PT.isPropPropTrunc

-- Any function that splits is a surjection:
isSplit→isSurjection : (f : X → Y) → isSplit f → isSurjection f
isSplit→isSurjection f = PT.elim
  (λ _ → isPropIsSurjection)
  (uncurry λ g → section→isSurjection)

-- Conversely, we can ask whether every surjection between sets splits:
AllSurjectionsSplit : (ℓ : Level) → Type _
AllSurjectionsSplit ℓ = ∀ (X Y : hSet ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) → isSurjection f → isSplit f

isPropAllSurjectionsSplit : isProp (AllSurjectionsSplit ℓ)
isPropAllSurjectionsSplit = isPropΠ4 λ { _ _ f _ → isPropIsSplit f }

-- If we assume choice for the fibers of a function of sets,
-- then the function splits if it is a surjection.
module FiberChoice (X Y : hSet ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) where
  fiberSet : (y : ⟨ Y ⟩) → hSet _
  fiberSet y .fst = fiber f y
  fiberSet y .snd = isSetΣ (str X) λ x → isProp→isSet (str Y (f x) y)

  hasChoiceFiber→isSplitSurjection : hasSetChoice Y fiberSet → (isSurjection f → isSplit f)
  hasChoiceFiber→isSplitSurjection choice-fiber-f surj-f = goal where
    goal : isSplit f
    goal = PT.map (hasSection-fiberSection-Iso f .Iso.inv) (choice-fiber-f surj-f)

-- The axiom of choice implies that all surjections split.
ASC→AllSurjectionsSplit : ASC ℓ ℓ → AllSurjectionsSplit ℓ
ASC→AllSurjectionsSplit ac X Y f = hasChoiceFiber→isSplitSurjection has-set-choice where
  open FiberChoice X Y f using (hasChoiceFiber→isSplitSurjection ; fiberSet)

  has-set-choice : hasSetChoice Y fiberSet
  has-set-choice = ac Y fiberSet

-- For any family, the total space over the family comes with a canonical fibration
-- over the domain of the family.
--
-- If the projection splits whenever it is a surjection, then choice holds for the family.
module TotalFibration (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) where
  module T = Total ⟨ X ⟩ (⟨_⟩ ∘ Y)
  open T using (proj) public
  open T using (Total)

  TotalSet : hSet _
  TotalSet .fst = Total
  TotalSet .snd = T.isOfHLevelTotal 2 (str X) (str ∘ Y)

  mereInhFam-isSurjectionProj-Iso : Iso ((x : ⟨ X ⟩) → ∥ ⟨ Y x ⟩ ∥₁) (isSurjection proj)
  mereInhFam-isSurjectionProj-Iso = Isomorphism.codomainIsoDep
    λ (x : ⟨ X ⟩) → propTruncIso $ invIso $ T.fiberProj-Family-Iso x

  isSplitProj-mereSectionFam-Iso : Iso (isSplit proj) ∥ Section (λ x → ⟨ Y x ⟩) ∥₁
  isSplitProj-mereSectionFam-Iso = propTruncIso T.hasSectionProj-SectionFam-Iso

  surjectiveProjSplits→hasChoice : (isSurjection proj → isSplit proj) → hasSetChoice X Y
  surjectiveProjSplits→hasChoice proj-surj→split mere-inh-fam = goal where
    is-surjection-proj : isSurjection proj
    is-surjection-proj = mereInhFam-isSurjectionProj-Iso .Iso.fun mere-inh-fam

    goal : ∥ (∀ x → ⟨ Y x ⟩) ∥₁
    goal = isSplitProj-mereSectionFam-Iso .Iso.fun $ proj-surj→split is-surjection-proj

-- If all surjections between sets split, then the axiom of choice holds.
AllSurjectionsSplit→ACS : AllSurjectionsSplit ℓ → ASC ℓ ℓ
AllSurjectionsSplit→ACS split X Y = surjectiveProjSplits→hasChoice is-surj→is-split where
  open TotalFibration X Y using (TotalSet ; proj ; surjectiveProjSplits→hasChoice)
  is-surj→is-split : isSurjection proj → isSplit proj
  is-surj→is-split = split TotalSet X proj
