module GpdCont.Equiv where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (pathToEquiv ; EquivJ)
open import Cubical.Foundations.Transport using (transportComposite)
open import Cubical.Functions.FunExtEquiv using (funExtEquiv)

private
  variable
    ℓ : Level
    A B : Type ℓ

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

equivΠCodComp : ∀ {ℓ ℓ'} {A : Type ℓ} {F G H : A → Type ℓ'}
  → (α : (a : A) → F a ≃ G a)
  → (β : (a : A) → G a ≃ H a)
  → equivΠCod (λ a → α a ∙ₑ β a) ≡ equivΠCod α ∙ₑ equivΠCod β
equivΠCodComp α β = equivEq refl

symEquiv : ∀ {ℓ} {A : Type ℓ} {x y : A} → (x ≡ y) ≃ (y ≡ x)
symEquiv = strictEquiv sym sym

equivAdjointEquivExtCodomain : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → (e : A ≃ B) (f : C → A) (g : C → B)
  → (f ≡ invEq e ∘ g) ≃ (equivFun e ∘ f ≡ g)
equivAdjointEquivExtCodomain {C} e f g = invEquiv funExtEquiv ∙ₑ equivΠCod lemma ∙ₑ funExtEquiv where
  lemma : ∀ (c : C) → (f c ≡ invEq e (g c)) ≃ (equivFun e (f c) ≡ g c)
  lemma c = equivAdjointEquiv e

equivAdjointEquivExtDomain : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : Type ℓ'}
  → (e : A ≃ B) (f : B → C) (g : A → C)
  → (g ∘ invEq e ≡ f) ≃ (g ≡ f ∘ equivFun e)
equivAdjointEquivExtDomain {B} {C} =
  EquivJ
    (λ A e → (f : B → C) (g : A → C) → (g ∘ invEq e ≡ f) ≃ (g ≡ f ∘ equivFun e))
    (λ f g → idEquiv (g ≡ f))

lineEquiv : ∀ {A B : I → Type ℓ} (f : (i : I) → A i → B i)
  → (is-equiv₀ : isEquiv (f i0))
  → (is-equiv₁ : isEquiv (f i1))
  → ∀ φ → A φ ≃ B φ
lineEquiv f is-equiv₀ is-equiv₁ φ = λ where
  .fst → f φ
  .snd → isProp→PathP (λ i → isPropIsEquiv (f i)) is-equiv₀ is-equiv₁ φ

secEquiv : (e : A ≃ B) → ∀ (φ : I) → B ≃ B
secEquiv {B} e = lineEquiv (λ φ b → secEq e b φ) (equivIsEquiv (invEquiv e ∙ₑ e)) (idIsEquiv B)

retEquiv : (e : A ≃ B) → ∀ (φ : I) → A ≃ A
retEquiv {A} e = lineEquiv (λ φ a → retEq e a φ) (equivIsEquiv (e ∙ₑ invEquiv e)) (idIsEquiv A)

equivΠDomain : ∀ {ℓ ℓ'} {A₀ : Type ℓ} {A₁ : Type ℓ} {B : A₁ → Type ℓ'}
  → (e : A₀ ≃ A₁)
  → ((a₁ : A₁) → B a₁) ≃ ((a₀ : A₀) → B (equivFun e a₀))
equivΠDomain {A₀} {A₁} {B} e .fst = _∘ equivFun e
equivΠDomain {A₀} {A₁} {B} e .snd = EquivJ (λ A₀ e → isEquiv (_∘ equivFun e)) (idIsEquiv ((a₁ : A₁) → B a₁)) e

isSet→section-equivToIso : isSet A → isSet B → section (equivToIso {A = A} {B = B}) isoToEquiv
isSet→section-equivToIso set-A set-B = retIsEq {f = isoToEquiv} (isSet→isEquiv-isoToPath set-A set-B)
