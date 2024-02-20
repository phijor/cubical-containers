module GpdCont.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path using (PathP≡compPath)
open import Cubical.Foundations.Univalence as UA hiding (ua) public
open import Cubical.Foundations.Univalence using (ua-unglue ; unglueIsEquiv ; Glue)

private
  variable
    ℓ : Level
    A B C : Type ℓ

  ∂ : I → I
  ∂ i = i ∨ ~ i

opaque
  ua : ∀ {ℓ} {A B : Type ℓ} → A ≃ B → A ≡ B
  ua = UA.ua

  ua-system : {A B : Type ℓ} (e : A ≃ B) → ∀ φ → Partial (∂ φ) (Σ[ T ∈ Type ℓ ] T ≃ B)
  ua-system {A} {B} e φ = λ where
    (φ = i0) → A , e
    (φ = i1) → B , idEquiv B

  ua-unglue-isEquiv : (e : A ≃ B) → ∀ φ → isEquiv (ua-unglue e φ)
  ua-unglue-isEquiv {A} {B} e φ = unglueIsEquiv B (∂ φ) (ua-system e φ)

  ua-unglue-equiv′ : (e : A ≃ B) → ∀ φ → ua e φ ≃ B
  ua-unglue-equiv′ e φ .fst = ua-unglue e φ
  ua-unglue-equiv′ e φ .snd = ua-unglue-isEquiv e φ

  lineEquiv : {A B : I → Type ℓ} (f : (i : I) → A i → B i)
    → (is-equiv₀ : isEquiv (f i0))
    → (is-equiv₁ : isEquiv (f i1))
    → ∀ φ → A φ ≃ B φ
  lineEquiv f is-equiv₀ is-equiv₁ φ = λ where
    .fst → f φ
    .snd → isProp→PathP (λ i → isPropIsEquiv (f i)) is-equiv₀ is-equiv₁ φ

  ua-unglue-equiv : (e : A ≃ B) → ∀ φ → ua e φ ≃ B
  ua-unglue-equiv e φ .fst = ua-unglue e φ
  ua-unglue-equiv e φ .snd = isProp→PathP (λ i → isPropIsEquiv (ua-unglue e i)) (equivIsEquiv e) (idIsEquiv _) φ

  ua-comp-unglue-equiv : {A B C : Type ℓ} (f : A ≃ B) (g : B ≃ C) → ∀ φ → ua f φ ≃ C
  ua-comp-unglue-equiv {C} f g = lineEquiv (λ φ x → equivFun g (ua-unglue f φ x)) (equivIsEquiv (f ∙ₑ g)) (equivIsEquiv g)

  secEquiv : (e : A ≃ B) → ∀ (φ : I) → B ≃ B
  secEquiv {B} e = lineEquiv (λ φ b → secEq e b φ) (equivIsEquiv (invEquiv e ∙ₑ e)) (idIsEquiv B)

  uaCompEquivSquare : ∀ {A B C : Type ℓ} → (f : A ≃ B) (g : B ≃ C) → PathP (λ j → A ≡ ua g j) (ua f) (ua (f ∙ₑ g))
  uaCompEquivSquare {ℓ} {A} {B} {C} f g i j = Glue C {φ} system where
    φ : I
    φ = ∂ i ∨ ∂ j

    system : Partial φ (Σ[ T ∈ Type ℓ ] T ≃ C)
    system (i = i0) = ua f j , ua-comp-unglue-equiv f g j
    system (i = i1) = ua (f ∙ₑ g) j , ua-unglue-equiv (f ∙ₑ g) j
    system (j = i0) = A , f ∙ₑ g
    system (j = i1) = ua g i , ua-unglue-equiv g i

  uaCompEquiv′ : ∀ {A B C : Type ℓ} → (f : A ≃ B) (g : B ≃ C) → (ua f) ∙ (ua g) ≡ ua (f ∙ₑ g)
  uaCompEquiv′ {A} {B} {C} f g = transport (PathP≡compPath (ua f) (ua g) (ua (f ∙ₑ g))) (uaCompEquivSquare f g)

  uaInvEquiv′ : {A B : Type ℓ} (e : A ≃ B) → ua (invEquiv e) ≡ sym (ua e)
  uaInvEquiv′ {ℓ} {A} {B} e i j = Glue B {φ} system where
    φ : I
    φ = ∂ i ∨ ∂ j

    system : Partial φ (Σ[ T ∈ Type ℓ ] T ≃ B)
    system (i = i0) = ua (invEquiv e) j , ua-comp-unglue-equiv (invEquiv e) e j
    system (i = i1) = ua e (~ j) , ua-unglue-equiv e (~ j)
    system (j = i0) = B , secEquiv e i
    system (j = i1) = A , e
