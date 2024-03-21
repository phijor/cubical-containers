module GpdCont.Equiv where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport using (transportComposite)

pathToEquivSym : ∀ {ℓ} {A B : Type ℓ}
  → (p : A ≡ B)
  → pathToEquiv (sym p) ≡ invEquiv (pathToEquiv p)
pathToEquivSym p = equivEq lem where
  lem : transport (sym p) ≡ invEquiv (pathToEquiv p) .fst
  lem = funExt λ b → sym (transportRefl (transport (sym p) b))

pathToEquivComp : ∀ {ℓ} {A B C : Type ℓ}
  → (p : A ≡ B) (q : B ≡ C)
  → pathToEquiv (p ∙ q) ≡ pathToEquiv p ∙ₑ pathToEquiv q
pathToEquivComp p q = equivEq $ funExt $ transportComposite p q
