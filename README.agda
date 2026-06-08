{-# OPTIONS --lossy-unification #-}
module README where

open import GpdCont.Prelude
{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.HITs.SetQuotients.Base using (_/_)
open import Cubical.Categories.Category.Base using (Category ; _^op)

private
  variable
    ℓ : Level


{- Section 2: Quotient and Symmetric Containers -}

module 2·1-QuotientContainers where
  open import GpdCont.QuotientContainer.Base using (QCont)
  open import GpdCont.QuotientContainer.Examples using (UnorderedTuple ; UnorderedTupleExt ; _∼permute_)
  open import GpdCont.QuotientContainer.Eval using (⟦_⟧)
  open import GpdCont.QuotientContainer.Premorphism using (Premorphism) renaming (PremorphismEquiv to _≈′_)
  open import GpdCont.QuotientContainer.Morphism using (Morphism)
  open import GpdCont.QuotientContainer.Category using (QCONT)

  open import Cubical.Data.SumFin using (Fin)

  01-Definition : Type (ℓ-suc ℓ)
  01-Definition {ℓ} = QCont ℓ

  open QCont using (Shape)

  02-Example : (n : ℕ) → QCont ℓ-zero
  02-Example = UnorderedTuple

  03-Definition : QCont ℓ → (hSet ℓ → hSet ℓ)
  03-Definition = ⟦_⟧

  04-Example : ∀ {n} {X} → ⟨ ⟦ UnorderedTuple n ⟧ X ⟩ ≃ (Fin n → ⟨ X ⟩) / _∼permute_
  04-Example {n} {X} = UnorderedTupleExt n X

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
  open import GpdCont.SymmetricContainer.Base using (SymmetricContainer)
  open import GpdCont.SymmetricContainer.Morphism using (Morphism)
  open import GpdCont.SymmetricContainer.TwoCategory using (SymmContCat ; ⟦-⟧)
  open import GpdCont.SymmetricContainer.Eval using (⟦_⟧)
  open import GpdCont.SymmetricContainer.Examples using (CyclicList)

  open import GpdCont.TwoCategory.Base using (TwoCategory)
  open import GpdCont.TwoCategory.StrictFunctor using (StrictFunctor)
  open import GpdCont.TwoCategory.GroupoidEndo using (Endo)


  08-Definition : Type (ℓ-suc ℓ)
  08-Definition = SymmetricContainer _

  09-Definition : (F G : SymmetricContainer ℓ) → Type ℓ
  09-Definition = Morphism

  10-Definition : TwoCategory (ℓ-suc ℓ) ℓ ℓ
  10-Definition = SymmContCat _

  11-Defintion : (G : SymmetricContainer ℓ) → (hGroupoid ℓ → hGroupoid ℓ)
  11-Defintion = ⟦_⟧

  _ : StrictFunctor (SymmContCat ℓ) (Endo ℓ)
  _ = ⟦-⟧

  12-Example : SymmetricContainer ℓ-zero
  12-Example = CyclicList

module 2·3-LiftingQuotientContainers where
  open import Cubical.Algebra.Group.Base
  open import Cubical.Algebra.Group.Morphisms using (GroupHom)
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

  open import GpdCont.Group.FundamentalGroup using (π₁)
  open import GpdCont.GroupAction.Base using (Action)
  open import GpdCont.GroupAction.Faithful using (isFaithful ; isFaithful→isSetTruncAssociatedBundle)
  open import GpdCont.GroupAction.AssociatedBundle using (associatedBundle ; associatedBundleComponents≃Orbits ; Orbits)
  open import GpdCont.Delooping.Map using () renaming (map to 𝔹-map)
  open import GpdCont.SymmetricContainer.Base using (SymmetricContainer)
  open import GpdCont.QuotientContainer.Premorphism using (Premorphism)
  open import GpdCont.SymmetricContainer.Eval using (⟦_⟧)
  open import GpdCont.QuotientContainer.Examples using (UnorderedTuple ; Id ; UPair ; degenDup)
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
    open import GpdCont.Delooping G using (𝔹) public
    open import GpdCont.Delooping G as 𝔹G
      using ()
      renaming (𝔹 to 𝔹G)

    _ : Type ℓ
    _ = 𝔹G

    13-Proposition : {X : hGroupoid ℓX} → (Σ[ x₀ ∈ ⟨ X ⟩ ] GroupHom G (π₁ X x₀)) ≃ (𝔹G → ⟨ X ⟩)
    13-Proposition {X} = 𝔹G.recEquivHom {X = X}

  14-Definition : {G H : Group ℓ} → GroupHom G H → 𝔹 G → 𝔹 H
  14-Definition = 𝔹-map

  15-Definition : {G : Group ℓ} {X : hSet ℓ} (σ : Action G X) → (𝔹 G → hSet ℓ)
  15-Definition = associatedBundle

  -- Bundles associated to faithful actions are set-truncated.
  16-Proposition : {σ : Action {ℓ} G X} → isFaithful σ → (Y : hSet ℓ) → isSet (fiber (associatedBundle σ) Y)
  16-Proposition {σ} = isFaithful→isSetTruncAssociatedBundle {σ = σ}

  -- Any quotient container defines a symmetric container.
  17-Definition : QCont ℓ → SymmetricContainer ℓ
  17-Definition = QContDelooping

  -- Bundles associated to quotient containers are set-truncated.
  18-Proposition : (Q : QCont ℓ) (Y : hSet ℓ) → isSet (fiber (DeloopingPos Q) Y)
  18-Proposition = hasSetFibersDeloopingPos

  -- The (truncated) interpretation of a delooped container coincides with its ordinary interpretation as a set-endofunctor.
  19-Theorem : (Q : QCont ℓ) (X : hSet ℓ) → ⟨ Tr ⟦ QContDelooping Q ⟧ X ⟩ ≃ ⟨ ⟦ Q ⟧/ X ⟩
  19-Theorem = LiftEvalEquiv

  20-Lemma : {G : Group ℓ} {X : hSet ℓ} (σ : Action G X) → ∥ Σ[ x ∈ 𝔹 G ] ⟨ associatedBundle σ x ⟩ ∥₂ ≃ Orbits σ
  20-Lemma = associatedBundleComponents≃Orbits

  21-Example : Premorphism Id UPair (id _)
  21-Example = degenDup

{- Section 3: Action Containers -}
module 3-ActionContainers where
  open import GpdCont.ActionContainer.Base using (ActionContainer)
  open import GpdCont.ActionContainer.Morphism using (Morphism)
  open import GpdCont.ActionContainer.Category using (Act≃FamGroupAction) renaming (Act to ActCont)
  open import GpdCont.ActionContainer.Examples using (CyclicList)

  22-Defintion : Type (ℓ-suc ℓ)
  22-Defintion = ActionContainer _

  -- Cyclic lists as an action container, defined in terms of a ℤ-action:
  23-Example : ActionContainer ℓ-zero
  23-Example = CyclicList

  24-Definition : (F G : ActionContainer ℓ) → Type ℓ
  24-Definition = Morphism

  -- Action containers and their morphisms form a category
  25-Definition : Category (ℓ-suc ℓ) ℓ
  25-Definition = ActCont

  module 3·1-Algebra where
    open import GpdCont.GroupAction.Category using (GroupAction ; GroupActionᴰ)
    open import GpdCont.GroupAction.Pi using (GroupActionProducts)
    open import GpdCont.Categories.Family as Fam using (Fam)
    open import GpdCont.ActionContainer.Constant using (konst ; konst-exponential)
    open import GpdCont.ActionContainer.DirectProduct using (binProducts)
    open import GpdCont.Categories.Products using (Products)
    open import GpdCont.Categories.Coproducts using (Coproducts)

    open import Cubical.Categories.Equivalence using (_≃ᶜ_)
    open import Cubical.Categories.Exponentials using (Exponential)

    {-# INJECTIVE_FOR_INFERENCE Fam #-}
    {-# INJECTIVE_FOR_INFERENCE konst #-}
    {-# INJECTIVE_FOR_INFERENCE konst-exponential #-}

    -- The category of group actions and equivariant maps.
    -- It is defined as a category displayed over Group × Setᵒᵖ.
    26-Definition : Category (ℓ-suc ℓ) ℓ
    26-Definition {ℓ} = GroupAction ℓ where
      open import Cubical.Categories.Instances.Groups using (GroupCategory)
      open import Cubical.Categories.Instances.Sets using (SET)
      open import Cubical.Categories.Constructions.TotalCategory.Base using (∫C)
      open import Cubical.Categories.Constructions.BinProduct as Prod using (_×C_)
      open import Cubical.Categories.Displayed.Base using (Categoryᴰ)
      {-# INJECTIVE_FOR_INFERENCE _×C_ #-}

      _ : Categoryᴰ (GroupCategory {ℓ} ×C SET ℓ ^op) ℓ ℓ
      _ = GroupActionᴰ ℓ

      _ : GroupAction ℓ ≡ ∫C (GroupActionᴰ ℓ)
      _ = refl

    27-Theorem : ActCont {ℓ} ≃ᶜ Fam ℓ (GroupAction ℓ)
    27-Theorem = Act≃FamGroupAction

    -- The category of group actions has all products:
    28-Proposition : Products (GroupAction ℓ) ℓ
    28-Proposition = GroupActionProducts

    -- Action containers are closed under products and coproducts:
    29-Corollary : Products (Fam ℓ (GroupAction ℓ)) ℓ × Coproducts (Fam ℓ (GroupAction ℓ)) ℓ
    29-Corollary {ℓ} = FamProducts GroupActionProducts , FamCoproducts where
      open Fam.Products ℓ (GroupAction ℓ)
      open Fam.Coproducts ℓ (GroupAction ℓ)

    _ : hSet ℓ → ActionContainer ℓ
    _ = konst

    30-Proposition : ∀ {ℓ} (K : hSet ℓ) (C : ActionContainer ℓ) → Exponential (ActCont {ℓ}) (konst K) C (binProducts (konst K))
    30-Proposition = konst-exponential


{- Section 4: The 2-category of Action Containers -}
module 4-ActionContainers-2-Category where
  open import GpdCont.ActionContainer.Base using (ActionContainer)
  open import GpdCont.ActionContainer.Morphism renaming (Morphism to ActionContainerMorphism)
  open import GpdCont.ActionContainer.Delooping using (module Container ; module Morphism) renaming (module Functor to DeloopingFunctor)
  open import GpdCont.ActionContainer.Category renaming (Act to ActContCat)
  open import GpdCont.SymmetricContainer.Base using (SymmetricContainer)
  open import GpdCont.SymmetricContainer.Morphism using () renaming (Morphism to SymmMorphism)
  open import GpdCont.SymmetricContainer.WildCat using (hoSymmCont)
  open import GpdCont.WildCat.HomotopyCategory using (ho)

  open import Cubical.Categories.Functor.Base using (Functor)

  31-Proposition-1 : ActionContainer ℓ → SymmetricContainer ℓ
  31-Proposition-1 = Container.Delooping

  31-Proposition-2 : ∀ {F G : ActionContainer ℓ} → ActionContainerMorphism F G → SymmMorphism (Container.Delooping F) (Container.Delooping G)
  31-Proposition-2 = Morphism.Delooping

  -- Allthough symmetric containers do not form a category,
  -- we can consider its "homotopy category", i.e. the category obtained
  -- by set-truncating the type of container morphisms.
  -- In this case, delooping of containers *does* behave functorially:
  _ : Functor (ActContCat {ℓ}) (hoSymmCont ℓ)
  _ = DeloopingFunctor.Delooping _

  module 4·1-Groups where
    open import GpdCont.Group.TwoCategory using (TwoGroup)
    open import GpdCont.Delooping.Functor using (module TwoFunc)
    open import GpdCont.TwoCategory.Base using (TwoCategory)
    open import GpdCont.TwoCategory.StrictFunctor using (StrictFunctor)
    open import GpdCont.TwoCategory.StrictFunctor.LocalFunctor as LocalFunctor using (LocalFunctor)
    open import GpdCont.TwoCategory.HomotopyGroupoid using (hGpdCat)

    open TwoFunc using (𝔹)

    32-Definition : TwoCategory (ℓ-suc ℓ) ℓ ℓ
    32-Definition = TwoGroup _

    33-Lemma : StrictFunctor (TwoGroup ℓ) (hGpdCat ℓ)
    33-Lemma = 𝔹 _

    -- Delooping of groups is locally a weak equalence of categories
    34-Theorem : LocalFunctor.isLocallyWeakEquivalence (𝔹 ℓ)
    34-Theorem = TwoFunc.isLocallyWeakEquivalenceDelooping _

    35-Proposition : LocalFunctor.isLocallyFullyFaithful (𝔹 ℓ)
    35-Proposition = TwoFunc.isLocallyFullyFaithfulDelooping _

    36-Proposition : LocalFunctor.isLocallyEssentiallySurjective (𝔹 ℓ)
    36-Proposition = TwoFunc.isLocallyEssentiallySurjectiveDelooping _

  module 4·2-GroupActions where
    open import GpdCont.GroupAction.Base using (Action)
    open import GpdCont.GroupAction.Equivariant using (isEquivariantMap[_][_,_])
    open import GpdCont.GroupAction.TwoCategory using (GroupAction ; GroupActionᴰ)
    open import GpdCont.GroupAction.AssociatedBundle using (associatedBundle ; associatedBundleMap)
    open import GpdCont.GroupAction.Delooping as ActionDelooping renaming (𝔹ᴰ to 𝔹ᴰ ; ActionDelooping to ∫𝔹ᴰ)
    open import GpdCont.Delooping.Functor using (module TwoFunc)

    open import GpdCont.TwoCategory.Base using (TwoCategory)
    open import GpdCont.TwoCategory.StrictFunctor using (StrictFunctor)
    open import GpdCont.TwoCategory.StrictFunctor.LocalFunctor using (isLocallyWeakEquivalence)
    open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryᴰ ; module TotalTwoCategory)
    open import GpdCont.TwoCategory.Displayed.StrictFunctor using (StrictFunctorᴰ)
    open import GpdCont.TwoCategory.HomotopyGroupoid using (hGpdCat)

    open import GpdCont.Group.TwoCategory using (TwoGroup)
    open import GpdCont.SetBundle.Base using (SetBundle ; SetBundleᴰ)

    open import Cubical.Algebra.Group.Base using (Group)
    open import Cubical.Algebra.Group.Morphisms using (GroupHom)

    open TwoFunc using (𝔹)
    module 𝔹 {ℓ} = StrictFunctor (𝔹 ℓ)
    module 𝔹ᴰ {ℓ} = StrictFunctorᴰ (𝔹ᴰ ℓ)

    -- The 2-category of group actions is defined by displaying it over the 2-category of groups:
    37-Definition : TwoCategory (ℓ-suc ℓ) ℓ ℓ
    37-Definition {ℓ} = GroupAction ℓ where
      _ : TwoCategoryᴰ (TwoGroup ℓ) _ _ _
      _ = GroupActionᴰ ℓ

    -- The 2-category of set bundles, displayed over h-groupoids:
    38-Definition : TwoCategory (ℓ-suc ℓ) ℓ ℓ
    38-Definition {ℓ} = SetBundle ℓ where
      _ : TwoCategoryᴰ (hGpdCat ℓ) _ _ _
      _ = SetBundleᴰ ℓ

      _ : SetBundle ℓ ≡ TotalTwoCategory.∫ (hGpdCat ℓ) (SetBundleᴰ ℓ)
      _ = refl

    -- Any equivariant map f : X ← Y induces a map of associated bundles:
    39-Definition : {G H : Group ℓ} {X Y : hSet ℓ} (σ : Action G X) (τ : Action H Y)
      → (φ : GroupHom G H)
      → (f : ⟨ Y ⟩ → ⟨ X ⟩) → isEquivariantMap[ φ , f ][ σ , τ ]
      → (x : ⟨ 𝔹.₀ G ⟩) → ⟨ associatedBundle τ (𝔹.₁ φ x) ⟩ → ⟨ associatedBundle σ x ⟩
    39-Definition = associatedBundleMap

    -- Delooping induces a strict 2-functor taking a group action to its associated bundle:
    40-Definition : StrictFunctor (GroupAction ℓ) (SetBundle ℓ)
    40-Definition = ∫𝔹ᴰ _ where
      -- This functor is defined between total categories, over 𝔹 : Group → hGroupoid
      _ : StrictFunctorᴰ (𝔹 ℓ) (GroupActionᴰ ℓ) (SetBundleᴰ ℓ)
      _ = 𝔹ᴰ _

    module TwoGroup ℓ = TwoCategory (TwoGroup ℓ)
    module GroupActionᴰ {ℓ} = TwoCategoryᴰ (GroupActionᴰ ℓ)

    module _
      {ℓ : Level}
      {G H : TwoGroup.ob ℓ}
      {φ ψ : TwoGroup.hom ℓ G H}
      {r : TwoGroup.rel ℓ φ ψ}
      {Xᴳ : GroupActionᴰ.ob[ G ]}
      {Yᴴ : GroupActionᴰ.ob[ H ]}
      {fᴰ : GroupActionᴰ.hom[ φ ] Xᴳ Yᴴ}
      {gᴰ : GroupActionᴰ.hom[ ψ ] Xᴳ Yᴴ}
      where
      41-Lemma : (isEquiv (𝔹ᴰ.₁ {ℓ} {G} {H} {φ} {Xᴳ} {Yᴴ})) × (isEquiv (𝔹ᴰ.₂ {ℓ} {G} {H} {φ} {ψ} {r} {Xᴳ} {Yᴴ} {fᴰ} {gᴰ}))
      41-Lemma .fst = ActionDelooping.isEquiv-𝔹ᴰ₁ ℓ {G} {H} {φ} {Xᴳ} {Yᴴ}
      41-Lemma .snd = ActionDelooping.isEquiv-𝔹ᴰ₂ ℓ {G} {H} {φ} {ψ} {r} {Xᴳ} {Yᴴ} {fᴰ} {gᴰ}

    42-Theorem : isLocallyWeakEquivalence (∫𝔹ᴰ ℓ)
    42-Theorem = ActionDelooping.isLocallyWeakEquivalenceDelooping _

  module 4·3-Families where
    open import GpdCont.TwoCategory.Family.Base using (Fam ; Famᴰ)
    open import GpdCont.TwoCategory.Family.Functor using (FamFunctor ; FamFunctorᴰ)
    open import GpdCont.TwoCategory.Base using (TwoCategory)
    open import GpdCont.TwoCategory.StrictFunctor using (StrictFunctor ; idStrictFunctor)
    open import GpdCont.TwoCategory.HomotopySet using () renaming (SetEq to hSetCat)
    open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryᴰ)
    open import GpdCont.TwoCategory.Displayed.StrictFunctor using (StrictFunctorᴰ)

    private
      variable
        ℓo ℓh ℓr : Level
        C D : TwoCategory ℓo ℓh ℓr

    43-Definition : (C : TwoCategory ℓo ℓh ℓr) (ℓ : Level) → TwoCategory _ _ _
    43-Definition C ℓ = Fam C ℓ where
      _ : TwoCategoryᴰ (hSetCat ℓ) _ _ _
      _ = Famᴰ C ℓ

    44-Defintion : StrictFunctor C D → StrictFunctor (Fam C ℓ) (Fam D ℓ)
    44-Defintion {C} {D} {ℓ} F = FamFunctor F ℓ where
      _ : StrictFunctorᴰ (idStrictFunctor (hSetCat ℓ)) (Famᴰ C ℓ) (Famᴰ D ℓ)
      _ = FamFunctorᴰ F ℓ

    module 45-Proposition {ℓ} (F : StrictFunctor C D) where
      open import GpdCont.TwoCategory.Family.Properties
      open import GpdCont.TwoCategory.LocalCategory using (isLocallyStrict)
      open import GpdCont.TwoCategory.StrictFunctor.LocalFunctor
      open import GpdCont.Axioms.TruncatedChoice renaming (ASC to AxiomOfSetChoice)

      1-locally-ff : isLocallyFullyFaithful F → isLocallyFullyFaithful (FamFunctor F ℓ)
      1-locally-ff = isLocallyFullyFaithfulFam F ℓ

      2-locally-split-eso : isLocallySplitEssentiallySurjective F → isLocallySplitEssentiallySurjective (FamFunctor F ℓ)
      2-locally-split-eso = isLocallySplitEssentiallySurjectiveFam F ℓ

      3-locally-eso : AxiomOfSetChoice ℓ _ → isLocallyStrict C → isLocallyEssentiallySurjective F → isLocallyEssentiallySurjective (FamFunctor F ℓ)
      3-locally-eso = isLocallyEssentiallySurjectiveFam F ℓ

  module 4·3-ActionContainers {ℓ} where
    open import GpdCont.ActionContainer.Base using (ActionContainer)
    open import GpdCont.ActionContainer.Morphism using (Morphism)
    open import GpdCont.ActionContainer.AsFamily ℓ as AsFamily using () renaming (FamAction to ActCont ; FamActionᴰ to ActContᴰ)
    open import GpdCont.ActionContainer.AsSymmetricContainer ℓ using (isLocallyFullyFaithfulActToSymmCont)
    open import GpdCont.GroupAction.Base using (Action)
    open import GpdCont.GroupAction.TwoCategory using (GroupAction)
    open import GpdCont.Group.MapConjugator using (Conjugator ; isConjugator)
    open import GpdCont.SetBundle.Base ℓ using (SetBundle ; module SetBundleNotation)
    open import GpdCont.SetBundle.Summation ℓ as Summation using (SetBundleΣ)
    open import GpdCont.TwoCategory.Base using (TwoCategory)
    open import GpdCont.TwoCategory.StrictFunctor using (StrictFunctor) renaming (compStrictFunctor to _⋆F_)
    open import GpdCont.TwoCategory.StrictFunctor.LocalFunctor
    open import GpdCont.TwoCategory.Family.Base using (Fam ; Famᴰ)
    open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryᴰ)
    open import GpdCont.Connectivity using (isPathConnected)

    -- The 2-category of action containers, defined as a 2-category of families of group actions.
    46-Definition : TwoCategory (ℓ-suc ℓ) ℓ ℓ
    46-Definition = ActCont where
      _ : ActCont ≡ Fam (GroupAction ℓ) ℓ
      _ = refl

    module ActCont where
      open TwoCategory ActCont public
      open TwoCategoryᴰ ActContᴰ public

    -- Objects and 1-cells of this 2-category coincide with the defintion of
    -- action containers and their morphisms made earlier:
    _ : ActCont.ob ≃ ActionContainer ℓ
    _ = AsFamily.obEquiv

    _ : (F G : ActCont.ob) → ActCont.hom F G ≃ Morphism (AsFamily.ob→ F) (AsFamily.ob→ G)
    _ = AsFamily.homEquiv

    module _
      (E @ (S , Eᴰ) F @ (T , Fᴰ) : ActCont.ob)
      (u : ⟨ S ⟩ → ⟨ T ⟩)
      (f g : ActCont.hom[ u ] Eᴰ Fᴰ)
      where
        module _ (s : ⟨ S ⟩) where
          φ = f s .fst
          f′ = f s .snd .fst
          ψ = g s .fst
          g′ = g s .snd .fst

        module _ (t : ⟨ T ⟩) where
          τ = equivFun ∘ ((Fᴰ t .snd .snd) .Action.action)
          H = ⟨ Fᴰ t .fst ⟩

        _ : ∀ s → Conjugator (φ s) (ψ s) ≡ (Σ[ r ∈ H (u s) ] isConjugator (φ s) (ψ s) r)
        _ = λ s → refl

        47-Proposition : ActCont.rel (u , f) (u , g) ≃ ((s : ⟨ S ⟩) → Σ[ (r , _) ∈ Conjugator (φ s) (ψ s) ] f′ s ≡ g′ s ∘ (τ (u s) r))
        47-Proposition = AsFamily.relEquiv E F u f g

    module 48-Corollary where
      open import GpdCont.Axioms.TruncatedChoice renaming (ASC to AxiomOfSetChoice)

      {-# INJECTIVE_FOR_INFERENCE AsFamily.isLocallyWeakEquivalenceFam𝔹 #-}
      {-# INJECTIVE_FOR_INFERENCE AsFamily.Fam𝔹 #-}

      1-locally-ff : isLocallyFullyFaithful AsFamily.Fam𝔹
      1-locally-ff = AsFamily.isLocallyFullyFaithfulFam𝔹

      2-locally-weq : AxiomOfSetChoice ℓ ℓ → isLocallyWeakEquivalence AsFamily.Fam𝔹
      2-locally-weq = AsFamily.isLocallyWeakEquivalenceFam𝔹

    49-Definition : StrictFunctor (Fam SetBundle ℓ) SetBundle
    49-Definition = SetBundleΣ

    private
      module SetBundle = SetBundleNotation
      module FamSetBundle = TwoCategory (Fam SetBundle ℓ)

    50-Lemma : (x y : FamSetBundle.ob) → ((j : ⟨ x .fst ⟩) → isPathConnected ⟨ SetBundle.Base (x .snd j) ⟩) → Functor.isFullyFaithful (LocalFunctor SetBundleΣ x y)
    50-Lemma = Summation.isLocallyFullyFaithfulΣ-at-connBase

    51-Theorem : isLocallyFullyFaithful (AsFamily.Fam𝔹 ⋆F SetBundleΣ)
    51-Theorem = isLocallyFullyFaithfulActToSymmCont

{- Addendum (April 2026): Skeletal containers -}
