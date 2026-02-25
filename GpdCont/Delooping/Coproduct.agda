module GpdCont.Delooping.Coproduct where

open import GpdCont.Prelude
open import GpdCont.Group.FreeProduct

open import GpdCont.Delooping as Delooping using (𝔹)

open import Cubical.HITs.Pushout
open import Cubical.Foundations.Pointed.Base
open import Cubical.Algebra.Group.Base

module _ {ℓX ℓY} ((X , x₀) : Pointed ℓX) ((Y , y₀) : Pointed ℓY) where
  Wedge : Type (ℓ-max ℓX ℓY)
  Wedge = Pushout {A = Unit} (λ _ → x₀) (λ _ → y₀)

  Wedge∙L : Pointed (ℓ-max ℓX ℓY)
  Wedge∙L .fst = Wedge
  Wedge∙L .snd = inl x₀

  Wedge∙R : Pointed (ℓ-max ℓX ℓY)
  Wedge∙R .fst = Wedge
  Wedge∙R .snd = inr y₀

  Wedge∙ : Pointed (ℓ-max ℓX ℓY)
  Wedge∙ = Wedge∙L

𝔹FreeGroup≃Wedge𝔹 : ∀ {ℓG ℓH} (G : Group ℓG) (H : Group ℓH)
  → 𝔹 (FreeProductGroup G H) ≃ Wedge (𝔹 G , 𝔹.⋆) (𝔹 H , 𝔹.⋆)
𝔹FreeGroup≃Wedge𝔹 G H .fst = {!Delooping.elim !}
𝔹FreeGroup≃Wedge𝔹 G H .snd = {! !}
