module GpdCont.StrictGroupoid.Discrete where

open import GpdCont.Prelude
open import GpdCont.SetTruncation using (setTruncMapId)
open import GpdCont.StrictGroupoid.Base
open import GpdCont.StrictGroupoid.Morphism

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (isEquiv→isContrHasSection)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥ ; isProp⊥)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)

private
  variable
    ℓ : Level
    A : Type ℓ

isSet→StrictGroupoidStr : isSet A → StrictGroupoidStr A
isSet→StrictGroupoidStr is-set-A .StrictGroupoidStr.is-groupoid = isSet→isGroupoid is-set-A
isSet→StrictGroupoidStr is-set-A .StrictGroupoidStr.pt = equivFun (ST.setTruncIdempotent≃ is-set-A)
isSet→StrictGroupoidStr is-set-A .StrictGroupoidStr.pt-section = retEq (ST.setTruncIdempotent≃ is-set-A)

StrictGroupoidEmpty : StrictGroupoidStr ⊥
StrictGroupoidEmpty = isSet→StrictGroupoidStr $ isProp→isSet isProp⊥


discrete : hSet ℓ → StrictGroupoid ℓ
discrete = map-snd isSet→StrictGroupoidStr

discreteStrUnique : isSet A → isContr (StrictGroupoidStr A)
discreteStrUnique is-set-A = recordIsOfHLevel 0 $ isContrΣ
  (inhProp→isContr (isOfHLevelPath 2 is-set-A) isPropIsGroupoid)
  λ _ → isEquiv→isContrHasSection {f = ∣_∣₂} is-equiv-trunc where

  is-equiv-trunc : isEquiv ∣_∣₂
  is-equiv-trunc = isoToIsEquiv $ invIso (ST.setTruncIdempotentIso is-set-A)

-- disc₁ : (X Y : hSet ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) → StrictFun (disc₀ X) (disc₀ Y)
-- disc₁ X Y f .fst = f
-- disc₁ X Y f .snd = funExt $ ST.elim (λ _ → isOfHLevelPath 2 (str Y) _ _) λ _ → refl

trunc₀ : StrictGroupoid ℓ → hSet ℓ
trunc₀ (G , is-strict-G) = StrictGroupoidStr.Components is-strict-G

-- trunc₁ : (G H : StrictGroupoid ℓ) (φ : StrictFun G H) → ⟨ trunc₀ G ⟩ → ⟨ trunc₀ H ⟩
-- trunc₁ G H = ST.map ∘ fst

adj : (A : hSet ℓ) (B : StrictGroupoid ℓ)
  → StrictFun (discrete A) B ≃ (⟨ A ⟩ → ∥ ⟨ B ⟩ ∥₂)
adj _ _ .fst (g , is-strict-g) = ∣_∣₂ ∘ g
adj A*@(A , is-set-A) B*@(B , is-strict-B) .snd .equiv-proof f = goal where
  module B = StrictGroupoidStr is-strict-B
  lemma : isContr (Σ[ f ∈ (A → ∥ B ∥₂) ] {!B.pt ∘ f ≡ g !})
  lemma = {! !}

  goal : isContr (fiber (λ { (g , _) → ∣_∣₂ ∘ g }) f)
  goal .fst .fst = B.pt ∘ f , funExt (ST.elim (λ _ → B.is-groupoid _ _) λ a → cong B.pt (B.pt-section (f a)))
  goal .fst .snd = funExt λ a → B.pt-section (f a)
  goal .snd ((g , is-strict-g) , ∣g∣≡f) = ΣPathP (StrictFun≡' (discrete A*) B* (funExt {! !}) {! !} , {! !})

adj' : (A : StrictGroupoid ℓ) (B : hSet ℓ)
  → StrictFun A (discrete B) ≃ (∥ ⟨ A ⟩ ∥₂ → ⟨ B ⟩)
adj' A B = goal where
  module A = StrictGroupoidStr (str A)
  goal : _ ≃ _
  goal .fst (g , _) = g ∘ A.pt
  goal .snd .equiv-proof f .fst .fst = f ∘ ∣_∣₂ , funExt (ST.elim (λ _ → {! !}) λ a → cong f $ sym (A.pt-section ∣ a ∣₂))
  goal .snd .equiv-proof f .fst .snd = funExt λ x → cong f (A.pt-section x)
  goal .snd .equiv-proof f .snd ((g , is-strict-g) , p) =
    ΣPathP
      ( StrictFun≡' A (discrete B)
        (funExt λ a → sym (p ≡$ ∣ a ∣₂) ∙ sym (is-strict-g ≡$ ∣ a ∣₂))
        (λ a → {! !})
      , {! !}
      )
-- adj' _ _ .fst (g , _) = {!g ∘ A.pt !}
-- adj' _ _ .snd = {! !}
