open import GpdCont.Prelude

module GpdCont.Delooping.Properties {ℓ} (G : Type ℓ) (_·_ : G → G → G) where

open import GpdCont.Groups.Base
open import GpdCont.Delooping.Base G _·_ as Delooping using (𝔹)

open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

isPropSetTruncDelooping : isProp ∥ 𝔹 ∥₂
isPropSetTruncDelooping = ST.elim2 (λ s t → ST.isSetPathImplicit) conn-lemma where
  conn-lemma : (s t : 𝔹) → ST.∣ s ∣₂ ≡ ST.∣ t ∣₂
  conn-lemma = Delooping.elimProp {B = λ s → (t : 𝔹) → ST.∣ s ∣₂ ≡ ST.∣ t ∣₂}
    (λ s → isPropΠ λ t → ST.isSetSetTrunc _ _)
    (Delooping.elimProp (λ t → ST.isSetSetTrunc _ _) $ refl {x = ST.∣ Delooping.⋆ ∣₂})

isConnectedDelooping : isContr ∥ 𝔹 ∥₂
isConnectedDelooping = inhProp→isContr ST.∣ 𝔹.⋆ ∣₂ isPropSetTruncDelooping

deloopingGroupStr : GroupStr 𝔹
deloopingGroupStr .GroupStr.is-connected = isConnectedDelooping
deloopingGroupStr .GroupStr.is-groupoid = Delooping.isGroupoid𝔹
deloopingGroupStr .GroupStr.pt = Delooping.⋆
