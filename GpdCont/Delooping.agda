open import GpdCont.Prelude using (Type)
open import Cubical.Algebra.Group.Base

module GpdCont.Delooping {ℓ} (G : Type ℓ) (γ : GroupStr G) where

open import GpdCont.Delooping.Base G γ public
open import GpdCont.Delooping.Properties G γ public
