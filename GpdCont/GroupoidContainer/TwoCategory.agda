module GpdCont.GroupoidContainer.TwoCategory where

open import GpdCont.Prelude
open import GpdCont.GroupoidContainer.Base
open import GpdCont.GroupoidContainer.Morphism using (GContId)
open import GpdCont.GroupoidContainer.WildCat using (Eval ; EvalFunctor ; module EvalFunctor) renaming (GContCat to GroupoidContainerWildCat)
open import GpdCont.GroupoidContainer.Eval using (⟦-⟧-Path ; ⟦-⟧ᵗ-Path)
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.TwoDiscrete using (TwoDiscrete)
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.GroupoidEndo using (Endo)
open import GpdCont.WildCat.NatTrans using (WildNatTransPath)
open import GpdCont.WildCat.TypeOfHLevel using (idNat ; _⊛_)

open import GpdCont.GroupoidContainer.Morphism using (isGroupoidGContMorphism)
open import GpdCont.Polynomial using (poly⟨_,_⟩ ; Polynomial)

import      Cubical.Foundations.GroupoidLaws as GL
open import Cubical.WildCat.Base using (WildCat)
open import Cubical.WildCat.Functor using (WildFunctor ; WildNatTrans)

GroupoidContainerCat : (ℓ : Level) → TwoCategory (ℓ-suc ℓ) ℓ ℓ
GroupoidContainerCat ℓ = TwoDiscrete (GroupoidContainerWildCat ℓ) λ _ _ → isGroupoidGContMorphism

private
  module GroupoidContainerWildCat {ℓ} = WildCat (GroupoidContainerWildCat ℓ)
  ⟦-⟧-id-lax : ∀ {ℓ} (C : GCont ℓ) → idNat ℓ (Eval C) ≡ EvalFunctor.on-hom (GContId C)
  ⟦-⟧-id-lax C = WildNatTransPath (λ X → funExt λ x → ⟦-⟧ᵗ-Path C refl refl) λ { v i j x → poly⟨ Polynomial.shape x , v ∘ Polynomial.label x ⟩  }

  ⟦-⟧-trans-lax : ∀ {ℓ} {F G H : GCont ℓ} (f : GroupoidContainerWildCat.Hom[ F , G ]) (g : GroupoidContainerWildCat.Hom[ G , H ])
    → _⊛_ ℓ (EvalFunctor.on-hom f) (EvalFunctor.on-hom g) ≡ EvalFunctor.on-hom (f GroupoidContainerWildCat.⋆ g)
  ⟦-⟧-trans-lax {H} f g = WildNatTransPath (λ X → funExt λ x → ⟦-⟧ᵗ-Path H refl refl) λ { v i j x → poly⟨ {!_ !} , {! !} ⟩ }

⟦-⟧ : ∀ {ℓ} → LaxFunctor (GroupoidContainerCat ℓ) (Endo ℓ)
⟦-⟧ .LaxFunctor.F-ob = Eval
⟦-⟧ .LaxFunctor.F-hom = EvalFunctor.on-hom
⟦-⟧ .LaxFunctor.F-rel = cong EvalFunctor.on-hom
⟦-⟧ .LaxFunctor.F-rel-id = refl
⟦-⟧ .LaxFunctor.F-rel-trans = GL.cong-∙ EvalFunctor.on-hom
⟦-⟧ .LaxFunctor.F-trans-lax = ⟦-⟧-trans-lax
⟦-⟧ .LaxFunctor.F-trans-lax-natural = {! !}
⟦-⟧ .LaxFunctor.F-id-lax = ⟦-⟧-id-lax
⟦-⟧ .LaxFunctor.F-assoc f g h = {! !}
⟦-⟧ .LaxFunctor.F-unit-left = {! !}
⟦-⟧ .LaxFunctor.F-unit-right = {! !}
