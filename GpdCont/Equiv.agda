module GpdCont.Equiv where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv)
open import Cubical.Foundations.Univalence using (pathToEquiv ; EquivJ)
open import Cubical.Foundations.Transport using (transportComposite)
open import Cubical.Functions.FunExtEquiv using (funExtEquiv)

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
