module GpdCont.Axiom where

open import GpdCont.Prelude
open import GpdCont.Connectivity using (merelyInh≃is1Connected)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso ; section)
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma.Properties as Sigma using ()
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.Truncation.FromNegTwo as Tr using (∥_∥_)
open import Cubical.Functions.Surjection
open import Cubical.Functions.Fibration
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level
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

-- The usual axiom of choice: Merely (1-) inhabited families merely have sections.
hasSetChoice : (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) → Type _
hasSetChoice X Y = ((x : ⟨ X ⟩) → ∥ ⟨ Y x ⟩ ∥₁) → ∥ ((x : ⟨ X ⟩) → ⟨ Y x ⟩) ∥₁

AC₂₁ : (ℓ : Level) → Type _
AC₂₁ ℓ = ∀ (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) → hasSetChoice X Y

isPropHasChoice : (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) → isProp (hasSetChoice X Y)
isPropHasChoice _ _ = isPropΠ λ _ → PT.isPropPropTrunc

hasChoice₂₁≃hasSetChoice : ∀ (X : hSet ℓ) Y → hasSetChoice X Y ≃ hasChoice 2 1 X Y
hasChoice₂₁≃hasSetChoice X Y = equiv→ (equivΠCod λ x → Tr.propTrunc≃Trunc1) Tr.propTrunc≃Trunc1

-- A functions is split if it merely has a section.
isSplit : (f : X → Y) → Type _
isSplit {X} {Y} f = ∃[ g ∈ (Y → X) ] section f g

-- The classical axiom that every surjection between sets splits:
AllSurjectionsSplit : (ℓ : Level) → Type _
AllSurjectionsSplit ℓ = ∀ (X Y : hSet ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) → isSurjection f → isSplit f

-- If we assume choice for the fibers of a function of sets,
-- then the function splits if it is a surjection.
module FiberChoice (X Y : hSet ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) where
  private
    inhFiber-section-Iso : {X Y : Type ℓ} {f : X → Y} → Iso (∀ y → fiber f y) (Σ[ g ∈ (Y → X) ] section f g)
    inhFiber-section-Iso = Sigma.Σ-Π-Iso

  fiberSet : (y : ⟨ Y ⟩) → hSet _
  fiberSet y .fst = fiber f y
  fiberSet y .snd = isSetΣ (str X) λ x → isProp→isSet (str Y (f x) y)

  hasChoiceFiber→isSplitSurjection : hasSetChoice Y fiberSet → (isSurjection f → isSplit f)
  hasChoiceFiber→isSplitSurjection choice-fiber-f surj-f = goal where
    goal : isSplit f
    goal = PT.map (inhFiber-section-Iso .Iso.fun) (choice-fiber-f surj-f)

-- The axiom of choice implies that all surjections split.
AC₂₁→AllSurjectionsSplit : AC₂₁ ℓ → AllSurjectionsSplit ℓ
AC₂₁→AllSurjectionsSplit ac X Y f = hasChoiceFiber→isSplitSurjection (ac Y fiberSet) where
  open FiberChoice X Y f using (hasChoiceFiber→isSplitSurjection ; fiberSet)

-- For any family, the total space over the family comes with a canonical fibration
-- over the domain of the family.
--
-- If the projection splits whenever it is a surjection, then choice hold for the family.
module TotalFibration (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) where
  Total : Type _
  Total = Σ[ x ∈ ⟨ X ⟩ ] ⟨ Y x ⟩

  isSetTotal : isSet Total
  isSetTotal = isSetΣ (str X) (str ∘ Y)

  TotalSet : hSet _
  TotalSet .fst = Total
  TotalSet .snd = isSetTotal

  proj : Total → ⟨ X ⟩
  proj = fst

  proj-section→Fam-section : (Σ[ i ∈ (⟨ X ⟩ → Total) ] section proj i) → ∀ x → ⟨ Y x ⟩
  proj-section→Fam-section (i , sect-i) x = subst (λ · → ⟨ Y · ⟩) (sect-i x) (i x .snd)

  mereInhFam→isSurjection-proj : (∀ x → ∥ ⟨ Y x ⟩ ∥₁) → isSurjection proj
  mereInhFam→isSurjection-proj inh-fam x = PT.map (λ { y → (x , y) , refl {x = x} }) (inh-fam x)

  surjectiveProjSplits→hasChoice : (isSurjection proj → isSplit proj) → hasSetChoice X Y
  surjectiveProjSplits→hasChoice proj-surj→split mere-inh-fam = goal where
    is-surjection-proj : isSurjection proj
    is-surjection-proj = mereInhFam→isSurjection-proj mere-inh-fam

    goal : ∥ (∀ x → ⟨ Y x ⟩) ∥₁
    goal = PT.map proj-section→Fam-section $ proj-surj→split is-surjection-proj

-- If all surjections between sets split, then the axiom of choice holds.
AllSurjectionsSplit→AC₂₁ : AllSurjectionsSplit ℓ → AC₂₁ ℓ
AllSurjectionsSplit→AC₂₁ split X Y = surjectiveProjSplits→hasChoice is-surj→is-split where
  open TotalFibration X Y using (TotalSet ; proj ; surjectiveProjSplits→hasChoice)
  is-surj→is-split : isSurjection proj → isSplit proj
  is-surj→is-split = split TotalSet X proj

Section : (f : X → Y) → Type _
Section {X} {Y} f = Σ[ g ∈ (Y → X) ] section f g

-- Being "split" can be generalized to higher h-levels:
-- A function is n-split if it has an n-connected type of sections.
hasConnectedSections : (n : HLevel) (f : X → Y) → Type _
hasConnectedSections n f = isConnected n (Section f)

-- For n=1 the two notions coincide:
-- Being merely inhabited is the same as being 1-connected.
isSplit≃has1ConnectedSections : {f : X → Y} → isSplit f ≃ hasConnectedSections 1 f
isSplit≃has1ConnectedSections = merelyInh≃is1Connected
