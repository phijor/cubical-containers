module README where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.HITs.SetQuotients.Base using (_/_)
open import Cubical.Categories.Category.Base using (Category)

private
  variable
    ℓ : Level


{- Section 2: Quotient and Symmetric Containers -}

module 2·1-QuotientContainers where
  open import GpdCont.QuotientContainer.Base using (QCont)
  open import GpdCont.QuotientContainer.Examples using (UnorderedTuple)
  open import GpdCont.QuotientContainer.Eval using (⟦_⟧)
  open import GpdCont.QuotientContainer.Premorphism using (Premorphism) renaming (PremorphismEquiv to _≈′_)
  open import GpdCont.QuotientContainer.Morphism using (Morphism)
  open import GpdCont.QuotientContainer.Category using (QCONT)

  01-Definition : Type (ℓ-suc ℓ)
  01-Definition {ℓ} = QCont ℓ

  open QCont using (Shape)

  02-Example : (n : ℕ) → QCont ℓ-zero
  02-Example = UnorderedTuple

  03-Definition : QCont ℓ → (hSet ℓ → hSet ℓ)
  03-Definition = ⟦_⟧

  04-Example : ∀ {n} {X} → ⟦ UnorderedTuple n ⟧ X ≡ {! !}
  04-Example = {! !}

  05-Definition : (F G : QCont ℓ) → Type ℓ
  05-Definition F G = Σ[ u ∈ (F.Shape → G.Shape) ] Premorphism F G u where
    module F = QCont F
    module G = QCont G

  06-Definition : (F G : QCont ℓ) → Type ℓ
  06-Definition = Morphism

  _ : (F G : QCont ℓ) → Morphism F G ≃ (Σ[ u ∈ (Shape F → Shape G) ] (Premorphism F G u / _≈′_))
  _ = λ F G → Morphism F G ≃Σ

  07-Definition : Category (ℓ-suc ℓ) ℓ
  07-Definition = QCONT _

module 2·1-SymmetricContainers where
  {- TODO: Rename modules and definitions to symmetric container -}
  open import GpdCont.GroupoidContainer.Base using (GCont)
  open import GpdCont.GroupoidContainer.Morphism using () renaming (GContMorphism to Morphism)
  open import GpdCont.GroupoidContainer.TwoCategory using (GroupoidContainerCat ; ⟦-⟧)
  open import GpdCont.GroupoidContainer.Eval using (⟦_⟧)
  open import GpdCont.GroupoidContainer.Examples using (CyclicList)

  open import GpdCont.TwoCategory.Base using (TwoCategory)
  open import GpdCont.TwoCategory.LaxFunctor using (LaxFunctor)
  open import GpdCont.TwoCategory.GroupoidEndo using (Endo)
  

  08-Definition : Type (ℓ-suc ℓ)
  08-Definition = GCont _

  09-Definition : (F G : GCont ℓ) → Type ℓ
  09-Definition = Morphism

  10-Definition : TwoCategory (ℓ-suc ℓ) ℓ ℓ
  10-Definition = GroupoidContainerCat _

  11-Defintion : (G : GCont ℓ) → (hGroupoid ℓ → hGroupoid ℓ)
  11-Defintion = ⟦_⟧

  _ : LaxFunctor (GroupoidContainerCat ℓ) (Endo ℓ)
  _ = ⟦-⟧

  12-Example : GCont ℓ-zero
  12-Example = CyclicList

module 2·3-LiftingQuotientContainers where
  open import Cubical.Algebra.Group.Base
  open import Cubical.Algebra.Group.Morphisms using (GroupHom)
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

  open import GpdCont.Group.FundamentalGroup using (π₁)
  open import GpdCont.GroupAction.Base using (Action)
  open import GpdCont.GroupAction.Faithful using (isFaithful ; isFaithful→isSetTruncAssociatedBundle)
  open import GpdCont.GroupAction.AssociatedBundle using (associatedBundle ; associatedBundleComponents≃Orbits ; Orbits)
  open import GpdCont.Delooping.Map using (map)
  open import GpdCont.GroupoidContainer.Base using (GCont)
  open import GpdCont.QuotientContainer.Premorphism using (Premorphism)
  open import GpdCont.GroupoidContainer.Eval using (⟦_⟧)
  open import GpdCont.QuotientContainer.Examples using (UnorderedTuple ; degenDup)
  open import GpdCont.QuotientContainer.Base using (QCont)
  open import GpdCont.QuotientContainer.Delooping using (QContDelooping ; DeloopingPos ; hasSetFibersDeloopingPos)
  open import GpdCont.QuotientContainer.DeloopingEval using (LiftEvalEquiv ; Tr)
  open import GpdCont.QuotientContainer.Eval using () renaming (⟦_⟧ to ⟦_⟧/)

  private
    variable
      G : Group ℓ
      ℓX : Level
      X : hSet ℓ
  
  module _ (G : Group ℓ) where
    open import GpdCont.Delooping ⟨ G ⟩ (str G) using (𝔹) public
    open import GpdCont.Delooping ⟨ G ⟩ (str G) as 𝔹G
      using ()
      renaming (𝔹 to 𝔹G)

    _ : Type ℓ
    _ = 𝔹G

    13-Proposition : {X : hGroupoid ℓX} → (Σ[ x₀ ∈ ⟨ X ⟩ ] GroupHom G (π₁ X x₀)) ≃ (𝔹G → ⟨ X ⟩)
    13-Proposition {X} = 𝔹G.recEquivHom {X = X}

  14-Definition : {G H : Group ℓ} → GroupHom G H → 𝔹 G → 𝔹 H
  14-Definition = map

  15-Definition : {G : Group ℓ} {X : hSet ℓ} (σ : Action G X) → (𝔹 G → hSet ℓ)
  15-Definition = associatedBundle

  -- Bundles associated to faithful actions are set-truncated.
  16-Proposition : {σ : Action {ℓ} G X} → isFaithful σ → (Y : hSet ℓ) → isSet (fiber (associatedBundle σ) Y)
  16-Proposition {σ} = isFaithful→isSetTruncAssociatedBundle {σ = σ}

  -- Any quotient container defines a symmetric container.
  17-Definition : QCont ℓ → GCont ℓ
  17-Definition = QContDelooping

  -- Bundles associated to quotient containers are set-truncated.
  18-Proposition : (Q : QCont ℓ) (Y : hSet ℓ) → isSet (fiber (DeloopingPos Q) Y)
  18-Proposition = hasSetFibersDeloopingPos

  -- The (truncated) interpretation of a delooped container coincides with its ordinary interpretation as a set-endofunctor.
  19-Theorem : (Q : QCont ℓ) (X : hSet ℓ) → ⟨ Tr ⟦ QContDelooping Q ⟧ X ⟩ ≃ ⟨ ⟦ Q ⟧/ X ⟩
  19-Theorem = LiftEvalEquiv

  20-Lemma : {G : Group ℓ} {X : hSet ℓ} (σ : Action G X) → ∥ Σ[ x ∈ 𝔹 G ] ⟨ associatedBundle σ x ⟩ ∥₂ ≃ Orbits σ
  20-Lemma = associatedBundleComponents≃Orbits

  21-Example : Premorphism (UnorderedTuple 1) (UnorderedTuple 2) (id _)
  21-Example = degenDup
