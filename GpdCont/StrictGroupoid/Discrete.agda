module GpdCont.StrictGroupoid.Discrete where

open import GpdCont.Prelude
open import GpdCont.StrictGroupoid.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (isEquiv→isContrHasSection)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)

private
  variable
    ℓ : Level
    A : Type ℓ

isSet→StrictGroupoidStr : isSet A → StrictGroupoidStr A
isSet→StrictGroupoidStr is-set-A .StrictGroupoidStr.is-groupoid = isSet→isGroupoid is-set-A
isSet→StrictGroupoidStr is-set-A .StrictGroupoidStr.pt = equivFun (ST.setTruncIdempotent≃ is-set-A)
isSet→StrictGroupoidStr is-set-A .StrictGroupoidStr.pt-section = retEq (ST.setTruncIdempotent≃ is-set-A)

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
