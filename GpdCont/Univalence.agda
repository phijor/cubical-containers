module GpdCont.Univalence where

open import GpdCont.Prelude
open import Cubical.Foundations.Equiv using (_∙ₑ_)
open import Cubical.Foundations.Path as Path using ()
open import Cubical.Foundations.Univalence as UA hiding (ua) public

opaque
  ua : ∀ {ℓ} {A B : Type ℓ} → A ≃ B → A ≡ B
  ua = UA.ua

  uaCompEquivSquare : ∀ {ℓ} {A B C : Type ℓ} → (e : A ≃ B) (f : B ≃ C) → PathP (λ j → A ≡ ua f j) (ua e) (ua (e ∙ₑ f))
  uaCompEquivSquare {A = A} {B = B} {C = C} e f = transport (sym $ Path.PathP≡compPath _ _ _) (sym $ uaCompEquiv e f)
