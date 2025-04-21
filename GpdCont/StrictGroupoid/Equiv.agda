module GpdCont.StrictGroupoid.Equiv where

open import GpdCont.StrictGroupoid.Base
open import GpdCont.StrictGroupoid.Morphism

open import GpdCont.Prelude
open import GpdCont.Univalence

open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)


module _ {ℓ} (G H : StrictGroupoid ℓ) where
  private
    module G = StrictGroupoidStr (str G)
    module H = StrictGroupoidStr (str H)

  isStrictGroupoidEquiv : StrictFun G H → Type _
  isStrictGroupoidEquiv (φ , _) = isEquiv φ

  StrictGroupoidEquiv : Type _
  StrictGroupoidEquiv = Σ[ σ ∈ StrictFun G H ] (isStrictGroupoidEquiv σ)

  mkStrictGroupoidEquiv : (σ : ⟨ G ⟩ ≃ ⟨ H ⟩) → StrictFunStr G H (equivFun σ) → StrictGroupoidEquiv
  mkStrictGroupoidEquiv (σ , σ-is-equiv) σ-is-strict .fst .fst = σ
  mkStrictGroupoidEquiv (σ , σ-is-equiv) σ-is-strict .fst .snd = σ-is-strict
  mkStrictGroupoidEquiv (σ , σ-is-equiv) σ-is-strict .snd = σ-is-equiv

  univalenceStrict : (G ≡ H) ≃ StrictGroupoidEquiv
  univalenceStrict =
    (G ≡ H) ≃⟨ invEquiv ΣPathP≃PathPΣ ⟩
    (Σ[ p ∈ ⟨ G ⟩ ≡ ⟨ H ⟩ ] PathP (λ i → StrictGroupoidStr (p i)) (str G) (str H)) ≃⟨ {! !} ⟩
    (Σ[ p ∈ ⟨ G ⟩ ≡ ⟨ H ⟩ ] PathP (λ i → ∥ p i ∥₂ → p i) G.pt H.pt) ≃⟨ invEquiv $ Σ-cong-equiv-fst (invEquiv univalence) ⟩
    (Σ[ σ ∈ ⟨ G ⟩ ≃ ⟨ H ⟩ ] PathP (λ i → ∥ ua σ i ∥₂ → ua σ i) G.pt H.pt) ≃⟨ Σ-cong-equiv-snd (λ σ → {! !}) ⟩
    (Σ[ σ ∈ ⟨ G ⟩ ≃ ⟨ H ⟩ ] StrictFunStr G H (equivFun σ)) ≃⟨ {! !} ⟩
    StrictGroupoidEquiv ≃∎

  uaStrict : StrictGroupoidEquiv → G ≡ H
  uaStrict = invEq univalenceStrict
