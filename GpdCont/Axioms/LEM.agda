module GpdCont.Axioms.LEM where

open import GpdCont.Prelude
open import GpdCont.Axioms.TruncatedChoice using (hasSetChoice)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (case_of_)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.HITs.Susp as Susp using (Susp ; north ; south ; merid)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; Discrete ; EquivPresDiscrete ; isPropDec)

LEM : (ℓ : Level) → Type (ℓ-suc ℓ)
LEM ℓ = (P : hProp ℓ) → Dec ⟨ P ⟩

DiscreteSetChoice : (ℓ : Level) → Type (ℓ-suc ℓ)
DiscreteSetChoice ℓ = ∀ (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ)
  → (∀ x → Discrete ⟨ Y x ⟩)
  → hasSetChoice X Y

private
  isSetBool* : ∀ {ℓ} → isSet (Bool* {ℓ})
  isSetBool* = isOfHLevelLift 2 isSetBool

  discreteBool* : ∀ {ℓ} → Discrete (Bool* {ℓ})
  discreteBool* = EquivPresDiscrete LiftEquiv _≟_

discreteDiaconescu : ∀ {ℓ} → DiscreteSetChoice ℓ → LEM ℓ
discreteDiaconescu {ℓ} disc-choice P = dec-P where
  Q : Type ℓ
  Q = ∥ Susp ⟨ P ⟩ ∥₂

  pole : Bool* {ℓ} → Q
  pole (lift true) = ∣ north ∣₂
  pole (lift false) = ∣ south ∣₂

  Fib : Q → Type ℓ
  Fib q = fiber pole q

  is-set-fib : ∀ q → isSet (Fib q)
  is-set-fib q = isSetΣ isSetBool* λ b → isOfHLevelPath 2 ST.isSetSetTrunc _ _

  discrete-fib : ∀ q → Discrete (Fib q)
  discrete-fib q = discreteΣProp discreteBool* λ b → ST.isSetSetTrunc _ _

  merely-inh-fib : ∀ q → ∥ Fib q ∥₁
  merely-inh-fib = ST.elim (λ q → isProp→isSet PT.isPropPropTrunc) λ where
    north → PT.∣ true* , refl ∣₁
    south → PT.∣ false* , refl ∣₁
    (merid p i) → isProp→PathP (λ i → PT.isPropPropTrunc {A = Fib ∣ merid p i ∣₂}) PT.∣ true* , refl ∣₁ PT.∣ false* , refl ∣₁ i

  merely-section-pole : ∥ (∀ q → Fib q) ∥₁
  merely-section-pole = disc-choice (Q , ST.isSetSetTrunc) (λ q → Fib q , is-set-fib q)
    discrete-fib
    merely-inh-fib

  Code : Q → hProp ℓ
  Code = ST.rec isSetHProp λ where
    north → Unit* , isPropUnit*
    south → P
    (merid p i) → ⇔toPath {P = Unit* , isPropUnit*} {Q = P} (λ _ → p) (λ _ → tt*) i

  decode : ∣ north ∣₂ ≡ ∣ south ∣₂ → ⟨ P ⟩
  decode q = subst (⟨_⟩ ∘ Code) q tt*

  dec-P : Dec ⟨ P ⟩
  dec-P = PT.rec (isPropDec $ str P) (λ s → dec* (fst ∘ s) (snd ∘ s)) merely-section-pole where
    dec* : (g : Q → Bool*) → (∀ q → pole (g q) ≡ q) → Dec ⟨ P ⟩
    dec* g sec = case (discreteBool* (g ∣ north ∣₂) (g ∣ south ∣₂)) of λ where
      (yes p) → yes (decode (sym (sec _) ∙∙ cong pole p ∙∙ sec _))
      (no ¬p) → no $ ¬p ∘ cong g ∘ cong ∣_∣₂ ∘ merid
