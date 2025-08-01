module GpdCont.HomotopyGroup.Subaction where

open import GpdCont.Prelude
open import GpdCont.Embedding
open import GpdCont.HomotopyGroup.Base
open import GpdCont.HomotopyGroup.Action
open import GpdCont.HomotopyGroup.Morphism
open import GpdCont.HomotopyGroup.Subgroup

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma


private
  variable
    ℓ ℓ′ ℓX ℓY : Level

module _ (G : hGroup ℓ) (H : hGroup ℓ′) (ι : hGroupHom G H) (ℓX : Level) (Y : hAction ℓY H) where
  private
    module ι = hGroupHom ι

  Subactionᴰ : Type _
  Subactionᴰ = Σ[ X ∈ hAction ℓX G ] ∀ g → ⟨ X g ⟩ ↪ ⟨ Y (ι.fun g) ⟩

  isSetSubactionᴰ : isSet Subactionᴰ
  isSetSubactionᴰ = isOfHLevelRespectEquiv 2 equiv is-set-emb where
    equiv : ((g : ⟨ G ⟩ᵗ) → Σ[ (X , _) ∈ Embedding ⟨ Y (ι.fun g) ⟩ ℓX ] isSet X) ≃ Subactionᴰ
    equiv =
      ((g : ⟨ G ⟩ᵗ) → Σ[ (X , _) ∈ Embedding ⟨ Y (ι.fun g) ⟩ ℓX ] isSet X) ≃⟨ equivΠCod (λ g → strictEquiv (λ { ((X , ι) , h) → ((X , h) , ι) }) (λ { ((X , h) , ι) → ((X , ι) , h) })) ⟩
      ((g : ⟨ G ⟩ᵗ) → Σ[ X ∈ hSet ℓX ] ⟨ X ⟩ ↪ ⟨ Y (ι.fun g) ⟩) ≃⟨ Σ-Π-≃ ⟩
      (Σ[ X ∈ hAction _ G ] ∀ g → ⟨ X g ⟩ ↪ ⟨ Y (ι.fun g) ⟩) ≃∎

    is-set-emb : isSet (∀ g → Σ[ (X , _) ∈ Embedding ⟨ Y (ι.fun g) ⟩ ℓX ] isSet X)
    is-set-emb = isSetΠ λ g → isSetΣSndProp isSetEmbedding λ _ → isPropIsSet

Subaction : (ℓ ℓX : Level) (H : hGroup ℓ′) (Y : hAction ℓY H) → Type _
Subaction ℓ ℓX H Y = Σ[ (G , ι) ∈ Mono ℓ H ] Subactionᴰ G H (ι .hGroupMono.hom) ℓX Y

isSetSubaction : (H : hGroup ℓ′) (Y : hAction ℓY H) → isSet (Subaction ℓ ℓX H Y)
isSetSubaction H Y = isSetΣ (isSetMono {H = H}) (λ { (G , ι) → isSetSubactionᴰ G H (ι .hGroupMono.hom) _ Y })
