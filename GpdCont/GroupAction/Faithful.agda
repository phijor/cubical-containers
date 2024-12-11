module GpdCont.GroupAction.Faithful where

open import GpdCont.Prelude
open import GpdCont.Univalence
open import GpdCont.HomotopySet
open import GpdCont.SetTruncation using (isEmbeddingCong→hasSetFibers)

open import GpdCont.Group.SymmetricGroup using (𝔖)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.AssociatedBundle using (associatedBundle ; associatedBundle-loop)
import      GpdCont.Delooping

open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding as Embedding using (isEmbedding)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms using (isMono)

{-# INJECTIVE_FOR_INFERENCE hSet≡ #-}

private
  variable
    ℓ : Level
    G : Group ℓ
    X : hSet ℓ
    σ : Action G X

isFaithful : (σ : Action G X) → Type _
isFaithful {G} σ = ∀ {g h : ⟨ G ⟩} → action g ≡ action h → g ≡ h where
  open Action σ using (action)

isPropIsFaithful : (σ : Action G X) → isProp (isFaithful σ)
isPropIsFaithful {G} σ = isPropImplicitΠ2 λ g h → isProp→ (G.is-set g h) where
  module G = GroupStr (str G)

isFaithful→isGroupHomMono : isFaithful σ → isMono (Action→GroupHom σ)
isFaithful→isGroupHomMono ff = ff

module _ {G : Group ℓ} {X : hSet ℓ} {σ : Action G X} (ff : isFaithful σ) where
  open Action σ using (action)
  private
    module 𝔹G = GpdCont.Delooping _ (str G)
    module G = GroupStr (str G)
    module 𝔖 = GroupStr (str $ 𝔖 X)

  isFaithful→isEmbeddingCong⟨-⟩∘AssocBundle : (x y : 𝔹G.𝔹) → isEmbedding (cong {x = x} {y = y} (⟨_⟩ ∘ associatedBundle σ))
  isFaithful→isEmbeddingCong⟨-⟩∘AssocBundle = goal where
    has-prop-fibers-σ : Embedding.hasPropFibers action
    has-prop-fibers-σ = Embedding.injective→hasPropFibers 𝔖.is-set ff

    is-embedding-σ : isEmbedding action
    is-embedding-σ = Embedding.hasPropFibers→isEmbedding has-prop-fibers-σ

    cong-assoc : (x y : 𝔹G.𝔹) → x ≡ y → ⟨ associatedBundle σ x ⟩ ≡ ⟨ associatedBundle σ y ⟩
    cong-assoc x y = cong {x = x} {y = y} (⟨_⟩ ∘ associatedBundle σ)

    comm' : cong-assoc 𝔹G.⋆ 𝔹G.⋆ ∘ 𝔹G.loop ≡ ua ∘ action
    comm' = funExt $ associatedBundle-loop σ

    comm : ua ∘ action ∘ 𝔹G.unloop ≡ cong-assoc 𝔹G.⋆ 𝔹G.⋆
    comm =
      ua ∘ action ∘ 𝔹G.unloop ≡[ i ]⟨ comm' i ∘ 𝔹G.unloop ⟩
      cong-assoc _ _ ∘ 𝔹G.loop ∘ 𝔹G.unloop ≡[ i ]⟨ cong-assoc 𝔹G.⋆ 𝔹G.⋆ ∘ (λ p → retEq 𝔹G.ΩDelooping≃ p i) ⟩
      cong-assoc 𝔹G.⋆ 𝔹G.⋆ ∎

    goal : ∀ (x y : 𝔹G.𝔹) → isEmbedding (cong-assoc x y)
    goal = 𝔹G.elimProp2 (λ _ _ → Embedding.isPropIsEmbedding) $
      subst isEmbedding comm $
        (Embedding.isEmbedding-∘ {f = ua}
          (Embedding.isEquiv→isEmbedding (isoToIsEquiv $ invIso univalenceIso))
          (Embedding.isEmbedding-∘ is-embedding-σ (Embedding.isEquiv→isEmbedding $ equivIsEquiv 𝔹G.ΩDelooping≃))
        )

  isFaithful→isEmbeddingCongAssocBundle : (x y : 𝔹G.𝔹) → isEmbedding (cong {x = x} {y = y} (associatedBundle σ))
  isFaithful→isEmbeddingCongAssocBundle x y = subst isEmbedding comm isEmbedding-composite where
    bundle≡ = hSet≡ {X = associatedBundle σ x} {Y = associatedBundle σ y}
    cong⟨-⟩∘associatedBundle = cong {x = x} {y = y} (⟨_⟩ ∘ associatedBundle σ)

    comm : bundle≡ ∘ cong⟨-⟩∘associatedBundle ≡ (cong {x = x} {y = y} (associatedBundle σ))
    comm =
      hSet≡ ∘ cong {x = x} {y = y} (⟨_⟩ ∘ associatedBundle σ) ≡⟨⟩
      hSet≡ ∘ cong ⟨_⟩ ∘ cong (associatedBundle σ) ≡[ i ]⟨ (λ p → hSet≡-section p i) ∘ cong (associatedBundle σ) ⟩
      (cong {x = x} {y = y} (associatedBundle σ)) ∎

    isEmbedding-bundle≡ : isEmbedding bundle≡
    isEmbedding-bundle≡ = Embedding.isEquiv→isEmbedding (equivIsEquiv hSet≡Equiv)

    isEmbedding-cong-assocBundle : isEmbedding cong⟨-⟩∘associatedBundle
    isEmbedding-cong-assocBundle = isFaithful→isEmbeddingCong⟨-⟩∘AssocBundle x y

    isEmbedding-composite : isEmbedding (bundle≡ ∘ cong {x = x} {y = y} (⟨_⟩ ∘ associatedBundle σ))
    isEmbedding-composite = Embedding.isEmbedding-∘ isEmbedding-bundle≡ isEmbedding-cong-assocBundle

  isFaithful→isSetTruncAssociatedBundle : (Y : hSet ℓ) → isSet (fiber (associatedBundle σ) Y)
  isFaithful→isSetTruncAssociatedBundle = isEmbeddingCong→hasSetFibers (associatedBundle σ) isFaithful→isEmbeddingCongAssocBundle
