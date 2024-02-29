open import GpdCont.Prelude using (Type)

module GpdCont.Delooping {ℓ} (G : Type ℓ) (_·_ : G → G → G) where

open import GpdCont.Delooping.Base G _·_ public
open import GpdCont.Delooping.Properties G _·_ public
