module README where

open import GpdCont.Prelude

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
  open import GpdCont.Delooping.Map using () renaming (map to 𝔹-map)
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
  14-Definition = 𝔹-map

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

{- Section 3: Action Containers -}
module 3-ActionContainers where
  open import GpdCont.ActionContainer.Abstract using (ActionContainer)
  open import GpdCont.ActionContainer.Morphism using (Morphism)
  open import GpdCont.ActionContainer.Category using (Act≃FamGroupAction) renaming (Act to ActCont)

  22-Defintion : Type (ℓ-suc ℓ)
  22-Defintion = ActionContainer _

  -- TODO: Cyclic lists as an action container
  23-Example : {! !}
  23-Example = {! !}

  24-Definition : (F G : ActionContainer ℓ) → Type ℓ
  24-Definition = Morphism

  -- Action containers and their morphisms form a category
  25-Definition : Category (ℓ-suc ℓ) ℓ
  25-Definition = ActCont

  module 3·1-Algebra where
    open import GpdCont.GroupAction.Category using (GroupAction ; GroupActionᴰ)
    open import GpdCont.DisplayedCategories using (Fam)
    open import GpdCont.ActionContainer.Constant using (konst ; konst-exponential)
    open import GpdCont.ActionContainer.DirectProduct using (binProducts)

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

    -- TODO: GroupAction has all products
    28-Proposition : {! !}
    28-Proposition = {! !}

    -- TODO: Action containers are closed under products and coproducts
    29-Corollary : {! !}
    29-Corollary = {! !}

    _ : hSet ℓ → ActionContainer ℓ
    _ = konst

    -- 30-Proposition : ∀ {ℓ} (K : hSet ℓ) (C : ActionContainer ℓ) → Exponential (ActCont {ℓ}) (konst K) C (binProducts konst K))
    30-Proposition = konst-exponential


{- Section 4: The 2-category of Action Containers -}
module 4-ActionContainers-2-Category where
  open import GpdCont.ActionContainer.Abstract using (ActionContainer)
  open import GpdCont.ActionContainer.Morphism renaming (Morphism to ActionContainerMorphism)
  open import GpdCont.ActionContainer.Delooping using (module Container ; module Morphism) renaming (module Functor to DeloopingFunctor)
  open import GpdCont.ActionContainer.Category renaming (Act to ActCont)
  open import GpdCont.GroupoidContainer.Base using (GCont)
  open import GpdCont.GroupoidContainer.Morphism using (GContMorphism)
  open import GpdCont.GroupoidContainer.WildCat using (GContCat)
  open import GpdCont.WildCat.HomotopyCategory using (ho)

  open import Cubical.Categories.Functor.Base using (Functor)

  31-Proposition-1 : ActionContainer ℓ → GCont ℓ
  31-Proposition-1 = Container.Delooping

  31-Proposition-2 : ∀ {F G : ActionContainer ℓ} → ActionContainerMorphism F G → GContMorphism (Container.Delooping F) (Container.Delooping G)
  31-Proposition-2 = Morphism.Delooping

  -- Allthough symmetric containers do not form a category,
  -- we can consider its "homotopy category", i.e. the category obtained
  -- by set-truncating the type of container morphisms.
  -- In this case, delooping of containers *does* behave functorially:
  _ : Functor (ActCont {ℓ}) (ho (GContCat ℓ))
  _ = DeloopingFunctor.Delooping _

  module 4·1-Groups where
    open import GpdCont.Group.TwoCategory using (TwoGroup)
    open import GpdCont.Delooping.Functor using (module TwoFunc)
    open import GpdCont.TwoCategory.Base using (TwoCategory)
    open import GpdCont.TwoCategory.LaxFunctor using (LaxFunctor)
    open import GpdCont.TwoCategory.LocalFunctor as LocalFunctor using (LocalFunctor)
    open import GpdCont.TwoCategory.HomotopyGroupoid using (hGpdCat)

    open TwoFunc renaming (TwoDelooping to 𝔹)

    32-Definition : TwoCategory (ℓ-suc ℓ) ℓ ℓ
    32-Definition = TwoGroup _

    33-Lemma : LaxFunctor (TwoGroup ℓ) (hGpdCat ℓ)
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
    open import GpdCont.GroupAction.Delooping as ActionDelooping renaming (𝔹ᴰ to 𝔹′ᴰ ; Delooping to 𝔹′)
    open import GpdCont.Delooping.Functor using (module TwoFunc)

    open import GpdCont.TwoCategory.Base using (TwoCategory)
    open import GpdCont.TwoCategory.LaxFunctor using (LaxFunctor)
    open import GpdCont.TwoCategory.LocalFunctor using (isLocallyWeakEquivalence)
    open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryᴰ ; module TotalTwoCategory)
    open import GpdCont.TwoCategory.Displayed.LaxFunctor using (LaxFunctorᴰ)
    open import GpdCont.TwoCategory.HomotopyGroupoid using (hGpdCat)

    open import GpdCont.Group.TwoCategory using (TwoGroup)
    open import GpdCont.SetBundle.Base using (SetBundle ; SetBundleᴰ)

    open import Cubical.Algebra.Group.Base using (Group)
    open import Cubical.Algebra.Group.Morphisms using (GroupHom)

    open TwoFunc renaming (TwoDelooping to 𝔹)
    module 𝔹 {ℓ} = LaxFunctor (𝔹 ℓ)
    module 𝔹′ᴰ {ℓ} = LaxFunctorᴰ (𝔹′ᴰ ℓ)

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

    40-Definition : LaxFunctorᴰ (𝔹 ℓ) (GroupActionᴰ ℓ) (SetBundleᴰ ℓ)
    40-Definition = 𝔹′ᴰ _

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
      41-Lemma : (isEquiv (𝔹′ᴰ.₁ {ℓ} {G} {H} {φ} {Xᴳ} {Yᴴ})) × (isEquiv (𝔹′ᴰ.₂ {ℓ} {G} {H} {φ} {ψ} {r} {Xᴳ} {Yᴴ} {fᴰ} {gᴰ}))
      41-Lemma .fst = ActionDelooping.isEquiv-𝔹₁ ℓ {G} {H} {φ} {Xᴳ} {Yᴴ}
      41-Lemma .snd = ActionDelooping.isEquiv-𝔹₂ ℓ {G} {H} {φ} {ψ} {r} {Xᴳ} {Yᴴ} {fᴰ} {gᴰ}

    42-Theorem : isLocallyWeakEquivalence (𝔹′ ℓ)
    42-Theorem = ActionDelooping.isLocallyWeakEquivalenceDelooping _
