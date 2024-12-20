module GpdCont.SymmetricContainer.TwoCategory where

open import GpdCont.Prelude
open import GpdCont.SymmetricContainer.Base
open import GpdCont.SymmetricContainer.Morphism using (idMorphism ; isGroupoidMorphism)
open import GpdCont.SymmetricContainer.WildCat using (Eval ; EvalFunctor ; module EvalFunctor ; SymmContWildCat)
open import GpdCont.SymmetricContainer.Eval using (⟦-⟧-Path ; ⟦-⟧ᵗ-Path)
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.TwoDiscrete using (TwoDiscrete)
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.GroupoidEndo using (Endo)
open import GpdCont.WildCat.NatTrans using (WildNatTransPath)
open import GpdCont.WildCat.TypeOfHLevel using (idNat ; _⊛_)

open import GpdCont.Polynomial using (poly⟨_,_⟩ ; Polynomial)

import      Cubical.Foundations.GroupoidLaws as GL
open import Cubical.WildCat.Base using (WildCat)
open import Cubical.WildCat.Functor using (WildFunctor ; WildNatTrans)

SymmContCat : (ℓ : Level) → TwoCategory (ℓ-suc ℓ) ℓ ℓ
SymmContCat ℓ = TwoDiscrete (SymmContWildCat ℓ) λ _ _ → isGroupoidMorphism

private
  module SymmContWildCat {ℓ} = WildCat (SymmContWildCat ℓ)
  ⟦-⟧-id-lax : ∀ {ℓ} (C : SymmetricContainer ℓ) → idNat ℓ (Eval C) ≡ EvalFunctor.on-hom (idMorphism C)
  ⟦-⟧-id-lax C = WildNatTransPath (λ X → funExt λ x → ⟦-⟧ᵗ-Path C refl refl) λ { v i j x → poly⟨ Polynomial.shape x , v ∘ Polynomial.label x ⟩  }

  ⟦-⟧-trans-lax : ∀ {ℓ} {F G H : SymmetricContainer ℓ} (f : SymmContWildCat.Hom[ F , G ]) (g : SymmContWildCat.Hom[ G , H ])
    → _⊛_ ℓ (EvalFunctor.on-hom f) (EvalFunctor.on-hom g) ≡ EvalFunctor.on-hom (f SymmContWildCat.⋆ g)
  ⟦-⟧-trans-lax {H} f g = WildNatTransPath (λ X → funExt λ x → ⟦-⟧ᵗ-Path H refl refl) λ { v i j x → poly⟨ {!_ !} , {! !} ⟩ }

⟦-⟧ : ∀ {ℓ} → LaxFunctor (SymmContCat ℓ) (Endo ℓ)
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
