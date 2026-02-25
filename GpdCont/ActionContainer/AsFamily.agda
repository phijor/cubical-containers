{-# OPTIONS --lossy-unification #-}

open import GpdCont.Prelude

module GpdCont.ActionContainer.AsFamily (ℓ : Level) where

open import GpdCont.ActionContainer.Base
open import GpdCont.ActionContainer.Morphism
open import GpdCont.Group.MapConjugator using (Conjugator)
open import GpdCont.GroupAction.Base using (Action ; _⁺_)
open import GpdCont.GroupAction.Equivariant using (isEquivariantMap[_][_,_])
open import GpdCont.GroupAction.TwoCategory using (GroupAction ; isLocallyStrictGroupAction)
open import GpdCont.GroupAction.Delooping as ActionDelooping using (ActionDelooping)
open import GpdCont.SetBundle.Base ℓ using (SetBundle)

open import GpdCont.TwoCategory.Base using (TwoCategory)
open import GpdCont.TwoCategory.StrictFunctor using (StrictFunctor)
open import GpdCont.TwoCategory.StrictFunctor.LocalFunctor as LocalFunctor using (LocalFunctor)
open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryᴰ)
open import GpdCont.TwoCategory.Family.Base using (Fam ; Famᴰ)
open import GpdCont.TwoCategory.Family.Functor using (FamFunctor)
open import GpdCont.TwoCategory.HomotopySet using (SetEq)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
import      Cubical.Foundations.Path as Path
open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

module SetEq = TwoCategory (SetEq ℓ)

FamSetBundle : TwoCategory (ℓ-suc ℓ) ℓ ℓ
FamSetBundle = Fam SetBundle ℓ

FamActionᴰ : TwoCategoryᴰ _ (ℓ-suc ℓ) ℓ ℓ
FamActionᴰ = Famᴰ (GroupAction ℓ) ℓ

FamAction : TwoCategory (ℓ-suc ℓ) ℓ ℓ
FamAction = Fam (GroupAction ℓ) ℓ

private
  module GroupAction = TwoCategory (GroupAction ℓ)

  module FamAction where
    open TwoCategory FamAction public
    open TwoCategoryᴰ FamActionᴰ public

obEquiv : FamAction.ob ≃ ActionContainer ℓ
obEquiv =
  (Σ[ S ∈ hSet ℓ ] (⟨ S ⟩ → Σ[ G ∈ Group ℓ ] Σ[ P ∈ hSet ℓ ] Action G P)) ≃⟨ Σ-cong-equiv-snd shuffle≃ ⟩
  (Σ[ S ∈ hSet ℓ ] Σ[ P ∈ (⟨ S ⟩ → hSet ℓ) ] Σ[ G ∈ (⟨ S ⟩ → Group ℓ) ] ((s : ⟨ S ⟩) → Action (G s) (P s))) ≃⟨ invEquiv ActionContainer≃Σ ⟩
  ActionContainer ℓ ≃∎
  where module _ (S : hSet ℓ) where
    shuffle : (⟨ S ⟩ → Σ[ G ∈ Group ℓ ] Σ[ P ∈ hSet ℓ ] Action G P) → (Σ[ P ∈ (⟨ S ⟩ → hSet ℓ) ] Σ[ G ∈ (⟨ S ⟩ → Group ℓ) ] ((s : ⟨ S ⟩) → Action (G s) (P s)))
    shuffle act .fst = λ s → act s .snd .fst
    shuffle act .snd .fst = λ s → act s .fst
    shuffle act .snd .snd = λ s → act s .snd .snd

    unshuffle : (Σ[ P ∈ (⟨ S ⟩ → hSet ℓ) ] Σ[ G ∈ (⟨ S ⟩ → Group ℓ) ] ((s : ⟨ S ⟩) → Action (G s) (P s))) → (⟨ S ⟩ → Σ[ G ∈ Group ℓ ] Σ[ P ∈ hSet ℓ ] Action G P)
    unshuffle (P , G , σ) = λ s → G s , P s , σ s

    shuffle≃ : _ ≃ _
    shuffle≃ = strictEquiv shuffle unshuffle

ob→ = equivFun obEquiv

homEquiv : (x y : FamAction.ob) → FamAction.hom x y ≃ Morphism (ob→ x) (ob→ y)
homEquiv x@(S , xᴰ) y@(T , yᴰ)  =
  Σ[ u ∈ (⟨ S ⟩ → ⟨ T ⟩) ] (∀ s → Σ[ φ ∈ GroupHom _ _ ] Σ[ f ∈ _ ] isEquivariantMap[ φ , f ][ σ s , τ (u s) ]) ≃⟨ Σ-cong-equiv-snd shuffle ⟩
  Σ[ u ∈ (⟨ S ⟩ → ⟨ T ⟩) ]
    Σ[ f ∈ ((s : ⟨ S ⟩) → ⟨ Q (u s) ⟩ → ⟨ P s ⟩) ]
    Σ[ φ ∈ (∀ s → ⟨ G s ⟩ → ⟨ H (u s) ⟩) ]
    Σ[ _ ∈ (∀ s → IsGroupHom (str $ G s) (φ s) (str $ H (u s))) ]
      (∀ s (g : ⟨ G s ⟩) → (((σ s) ⁺ g) ∘ (f s)) ≡ (f s ∘ (τ (u s) ⁺ φ s g)))
      ≃⟨ Σ-cong-equiv-snd (λ u → Σ≃ _) ⟩
  Σ[ u ∈ (⟨ S ⟩ → ⟨ T ⟩) ] (Morphismᴰ (ob→ x) (ob→ y) u) ≃⟨ Σ≃ _ ⟩
  Morphism (ob→ x) (ob→ y) ≃∎
  where
    open GpdCont.ActionContainer.Morphism (ob→ x) (ob→ y) using (MorphismᴰToΣ ; MorphismToΣ)
    module _ (s : ⟨ S ⟩) where
      G = xᴰ s .fst
      P = xᴰ s .snd .fst
      σ = xᴰ s .snd .snd

    module _ (t : ⟨ T ⟩) where
      H = yᴰ t .fst
      Q = yᴰ t .snd .fst
      τ = yᴰ t .snd .snd

    shuffle-iso : (u : ⟨ S ⟩ → ⟨ T ⟩)
      → Iso
        (∀ s → Σ[ φ ∈ GroupHom _ _ ] Σ[ f ∈ _ ] isEquivariantMap[ φ , f ][ σ s , τ (u s) ])
        ( Σ[ f ∈ ((s : ⟨ S ⟩) → ⟨ Q (u s) ⟩ → ⟨ P s ⟩) ]
          Σ[ φ ∈ (∀ s → ⟨ G s ⟩ → ⟨ H (u s) ⟩) ]
          Σ[ _ ∈ (∀ s → IsGroupHom (str $ G s) (φ s) (str $ H (u s))) ]
            (∀ s (g : ⟨ G s ⟩) → (((σ s) ⁺ g) ∘ (f s)) ≡ (f s ∘ (τ (u s) ⁺ φ s g)))
        )
    shuffle-iso u .Iso.fun f = (fst ∘ snd ∘ f) , (fst ∘ fst ∘ f) , (snd ∘ fst ∘ f) , (snd ∘ snd ∘ f)
    shuffle-iso u .Iso.inv (f , φ , φ-hom , f-eqva) s = (φ s , φ-hom s) , f s , f-eqva s
    shuffle-iso u .Iso.sec _ = refl
    shuffle-iso u .Iso.ret _ = refl

    shuffle : ∀ u → _ ≃ _
    shuffle u = strictIsoToEquiv (shuffle-iso u)

module _
  ((J , x) (K , y) : FamAction.ob)
  (u : ⟨ J ⟩ → ⟨ K ⟩)
  (f g : FamAction.hom[ u ] x y)
  where
    private
      module _ (j : ⟨ J ⟩) where
        φ = f j .fst
        f′ = f j .snd .fst
        ψ = g j .fst
        g′ = g j .snd .fst

      module _ (k : ⟨ K ⟩) where
        τ = equivFun ∘ ((y k .snd .snd) .Action.action)

      isContr-u≡u : isContr (u Eq.≡ u)
      isContr-u≡u = inhProp→isContr Eq.refl $
        isPropRetract
          Eq.eqToPath
          Eq.pathToEq
          Eq.pathToEq-eqToPath
          (isSet→ (str K) u u)

    relEquiv : FamAction.rel {y = (K , y)} (u , f) (u , g) ≃ ((j : ⟨ J ⟩) → Σ[ (r , _) ∈ Conjugator (φ j) (ψ j) ] f′ j ≡ g′ j ∘ (τ (u j) r))
    relEquiv = Σ-contractFst isContr-u≡u

private
  𝔹ᴬ = ActionDelooping ℓ
  module 𝔹ᴬ = StrictFunctor 𝔹ᴬ

Fam𝔹 : StrictFunctor FamAction FamSetBundle
Fam𝔹 = FamFunctor (ActionDelooping ℓ) ℓ

private
  module Fam𝔹 where
    open StrictFunctor Fam𝔹 public
    open import GpdCont.TwoCategory.Family.Properties (ActionDelooping ℓ) ℓ public

module _ where
  open import GpdCont.Axioms.TruncatedChoice renaming (ASC to AxiomOfSetChoice)
  open LocalFunctor Fam𝔹

  isLocallyFullyFaithfulFam𝔹 : isLocallyFullyFaithful
  isLocallyFullyFaithfulFam𝔹 = Fam𝔹.isLocallyFullyFaithfulFam (ActionDelooping.isLocallyFullyFaithfulDelooping ℓ)

  module _ (choice : AxiomOfSetChoice ℓ ℓ) where
    isLocallyEssentiallySurjectiveFam𝔹 : isLocallyEssentiallySurjective
    isLocallyEssentiallySurjectiveFam𝔹 = Fam𝔹.isLocallyEssentiallySurjectiveFam
      choice
      (isLocallyStrictGroupAction ℓ)
      (ActionDelooping.isEssentiallySurjectiveDelooping ℓ)

    isLocallyWeakEquivalenceFam𝔹 : isLocallyWeakEquivalence
    isLocallyWeakEquivalenceFam𝔹 = isLocallyFullyFaithful×EssentiallySurjective→isLocallyWeakEquivalence
      isLocallyFullyFaithfulFam𝔹
      isLocallyEssentiallySurjectiveFam𝔹
