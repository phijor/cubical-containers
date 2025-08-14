module GpdCont.PropositionalTruncation where

open import GpdCont.Prelude
open import GpdCont.Prelude.Notation

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.PropositionalTruncation public
open import Cubical.HITs.PropositionalTruncation.Monad public

private
  variable
    ℓ ℓA ℓB : Level
    A B : Type ℓ

propTruncIso : Iso A B → Iso ∥ A ∥₁ ∥ B ∥₁
propTruncIso is = ∥is∥ where
  open Iso
  ∥is∥ : Iso _ _
  ∥is∥ .fun = PT.map (is .fun)
  ∥is∥ .inv = PT.map (is .inv)
  ∥is∥ .rightInv _ = PT.isPropPropTrunc _ _
  ∥is∥ .leftInv _ = PT.isPropPropTrunc _ _

propTruncFstΣ≃ : ∀ {B : A → Type ℓ}
  → isProp A
  → ∥ Σ A B ∥₁ ≃ Σ A (∥_∥₁ ∘ B)
propTruncFstΣ≃ {A} {B} is-prop-A = isoToEquiv trunc-iso where
  is-prop-Σ : isProp (Σ A (∥_∥₁ ∘ B))
  is-prop-Σ = isPropΣ is-prop-A (λ _ → PT.isPropPropTrunc)
  trunc-iso : Iso ∥ Σ A B ∥₁ (Σ A (∥_∥₁ ∘ B))
  trunc-iso .Iso.fun = PT.rec is-prop-Σ (λ { (a , b) → (a , PT.∣ b ∣₁) })
  trunc-iso .Iso.inv = uncurry λ a → PT.map (a ,_)
  trunc-iso .Iso.rightInv = uncurry λ a → PT.elim (λ _ → isOfHLevelPath 1 is-prop-Σ _ _) λ _ → refl
  trunc-iso .Iso.leftInv = PT.elim (λ _ → isOfHLevelPath 1 PT.isPropPropTrunc _ _) λ _ → refl

untrunc : isProp A → ∥ A ∥₁ → A
untrunc is-prop-A = PT.rec is-prop-A (id _)

instance
  propTruncDo : Do ∥_∥₁
  propTruncDo .Do._>>=_ x f = PT.rec PT.isPropPropTrunc f x
  propTruncDo .Do.pure = PT.∣_∣₁

choiceMap : ∀ {B : A → Type ℓB} → ∥ ((a : A) → B a) ∥₁ → (a : A) → ∥ B a ∥₁
choiceMap = PT.rec (isPropΠ λ a → isPropPropTrunc) λ f a → ∣ f a ∣₁

satChoice : (A : Type ℓA) (ℓB : Level) → Type _
satChoice A ℓB = ∀ (B : A → Type ℓB) → isEquiv (choiceMap {B = B})

isPropSatChoice : isProp (satChoice A ℓB)
isPropSatChoice = isPropΠ λ B → isPropIsEquiv _

module Choice (choice : satChoice A ℓB) where
  pick : {B : A → Type ℓB} → ∥ (∀ a → B a) ∥₁ → (∀ a → ∥ B a ∥₁)
  pick = choiceMap

  equiv : {B : A → Type ℓB} → ∥ (∀ a → B a) ∥₁ ≃ (∀ a → ∥ B a ∥₁)
  equiv .fst = choiceMap
  equiv .snd = choice _

  choose : {B : A → Type ℓB} → (∀ a → ∥ B a ∥₁) → ∥ (∀ a → B a) ∥₁
  choose {B} = invIsEq (choice B)
