module GpdCont.Axioms.AxiomK where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (isSet→SquareP)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using (Jequiv)
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma

open import Cubical.Axiom.UniquenessOfIdentity as UIP using (AxiomK ; UIP) public

private
  variable
    ℓ ℓ' ℓP : Level
    A : Type ℓ
    B : A → Type ℓ'

isSet→AxiomK : isSet A → AxiomK A ℓ'
isSet→AxiomK is-set-A = UIP.UIP→AxiomK (UIP.isSet→UIP is-set-A) _

AxiomKRefl : (K : AxiomK A ℓ') → Type _
AxiomKRefl {A} {ℓ'} K =
  (x : A) (P : x ≡ x → Type ℓ')
  → (d : P refl)
  → K x P d refl ≡ d

isSet→AxiomKRefl : (is-set-A : isSet A) → AxiomKRefl {ℓ' = ℓ'} (isSet→AxiomK is-set-A)
isSet→AxiomKRefl is-set-A x P d = goal where
  r : refl ≡ refl
  r = UIP.isSet→UIP is-set-A x refl
  lem : Square r refl refl refl
  lem = isSet→SquareP (λ _ _ → isProp→isSet (is-set-A x x)) _ _ _ _

  goal : subst P r d ≡ d
  goal = cong (λ p → subst P p d) lem ∙ substRefl {B = P} d

Kequiv : (K : ∀ {ℓ'} → AxiomK A ℓ') (K-refl : AxiomKRefl K)
  → (x : A) → (P : x ≡ x → Type ℓ')
  → P refl ≃ (∀ p → P p)
Kequiv {A} K K-refl x P = λ where
  .fst → K x P
  .snd .equiv-proof p* .fst → p* refl , refl-fib p*
  .snd .equiv-proof p* .snd (d , Kd≡p*) → ΣPathP (d-fib d Kd≡p* , {!funExtDep !})
    where
      refl-fib : ∀ p* → K x P (p* refl) ≡ p*
      refl-fib p* = funExt (K x (λ x≡x → K x P (p* refl) x≡x ≡ p* x≡x) (K-refl x P (p* refl)))

      d-fib : ∀ {p*} → (d : P refl) → K x P d ≡ p* → p* refl ≡ d
      d-fib d Kd≡p* = sym (funExt⁻ Kd≡p* refl) ∙ K-refl x P d

      uip : UIP A
      uip x x≡x = K x (refl ≡_) refl x≡x

isSet→Kequiv : isSet A → (x : A) → (P : x ≡ x → Type ℓ') → P refl ≃ (∀ p → P p)
isSet→Kequiv is-set-A = Kequiv (isSet→AxiomK is-set-A) (isSet→AxiomKRefl is-set-A)

private
  K-subst : isSet A → (x : A) (P : x ≡ x → Type ℓ') → ∀ p → P p ≃ P refl
  K-subst is-set-A x P p = pathToEquiv (cong P (is-set-A _ _ p refl))

-- foo : isSet A
--   → (_R⟨_⟩_ : ∀ {a₀ a₁} → B a₀ → a₀ ≡ a₁ → B a₁ → Type ℓ')
--   → {a₀ a₁ : A}
--   → (b b′ : B a₀)
--   → (Σ[ p ∈ a₀ ≡ a₁ ] b R⟨ p ⟩ b′) ≃ ((a₀ ≡ a₁) × Σ[ b′ ∈ B a₀ ] b R⟨ refl ⟩ b′ )
  -- → (b R⟨ refl ⟩ b′) ≃ (∀ {a₁} (p : a₀ ≡ a₁) (b′ : B a₁) → b R⟨ p ⟩ b′)

KΣContr : isSet A
  → (_R⟨_⟩_ : ∀ {a₀ a₁} → B a₀ → a₀ ≡ a₁ → B a₁ → Type ℓ')
  → {a₀ : A}
  → (b b′ : B a₀)
  → (b R⟨ refl ⟩ b′) ≃ (∀ {a₁} (p : a₀ ≡ a₁) (b′ : B a₁) → b R⟨ p ⟩ b′)
KΣContr {A} {B} is-set-A _R⟨_⟩_ {a₀} b b′ =
  (b R⟨ refl ⟩ b′) ≃⟨ isSet→Kequiv is-set-A a₀ (λ r → b R⟨ r ⟩ b′) ⟩
  ((p : a₀ ≡ a₀) → b R⟨ p ⟩ b′) ≃⟨ {! !} ⟩
  ((b′ : B a₀) → b R⟨ refl ⟩ b′) ≃⟨ Jequiv (λ a₁ (p : a₀ ≡ a₁) → ∀ b′ → b R⟨ p ⟩ b′) ⟩
  (∀ {a₁} (p : a₀ ≡ a₁) (b′ : B a₁) → b R⟨ p ⟩ b′) ≃∎

  -- isSet→Kequiv is-set-A a₀ (λ r → b R⟨ r ⟩ b′) ∙ₑ {!K-subst is-set-A _ (λ r → b R⟨ r ⟩ b′) !} ∙ₑ {!  !}
  -- Σ[ p ∈ x ≡ y ] (P y p) ≃⟨ {!Σ-cong-equiv-snd {A = x ≡ y} {B = P y} {B' = λ _ → P x refl} !} ⟩
  -- P x refl ≃∎

data Ford {ℓ ℓ'} {A : Type ℓ} (x : A) (P : x ≡ x → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  ford : (d : P refl) → Ford x P

