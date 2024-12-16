module GpdCont.SetQuotients where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv using (equivToIso)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_] ; eq/)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B : Type ℓ
    R S : A → A → Type ℓ'

open Iso

map : (f : A → B) (pres : ∀ {a a'} → R a a' → S (f a) (f a')) → A / R → B / S
map f pres = SQ.rec SQ.squash/ ([_] ∘ f) λ a a' p → eq/ _ _ (pres p)

module _
  (isoA : Iso A B)
  (presS : ∀ {a a'} → R a a' → S (isoA .fun a) (isoA .fun a'))
  (presR : ∀ {b b'} → S b b' → R (isoA .inv b) (isoA .inv b'))
  where
  relBiimpl→QuotIso : Iso (A / R) (B / S)
  relBiimpl→QuotIso .fun = map (isoA .fun) presS
  relBiimpl→QuotIso .inv = map (isoA .inv) presR
  relBiimpl→QuotIso .rightInv = SQ.elimProp (λ _ → _/_.squash/ _ _) λ a → cong [_] (isoA .rightInv a)
  relBiimpl→QuotIso .leftInv = SQ.elimProp (λ _ → _/_.squash/ _ _) λ b → cong [_] (isoA .leftInv b)

  relBiimpl→QuotEquiv : (A / R) ≃ (B / S)
  relBiimpl→QuotEquiv = isoToEquiv relBiimpl→QuotIso

module _
  {A : Type ℓ}
  {R S : A → A → Type ℓ'}
  (presS : ∀ {a a'} → R a a' → S a a')
  (presR : ∀ {a a'} → S a a' → R a a')
  where
  relBiimpl→QuotIdIso : Iso (A / R) (A / S)
  relBiimpl→QuotIdIso = relBiimpl→QuotIso idIso presS presR

  relBiimpl→QuotIdEquiv : (A / R) ≃ (A / S)
  relBiimpl→QuotIdEquiv = relBiimpl→QuotEquiv idIso presS presR

relIso→QuotIdIso : {R S : A → A → Type ℓ'} → (∀ {a a'} → Iso (R a a') (S a a')) → Iso (A / R) (A / S)
relIso→QuotIdIso rel-iso = relBiimpl→QuotIdIso (rel-iso .fun) (rel-iso .inv)

relEquiv→QuotIdEquiv : {R S : A → A → Type ℓ'} → (∀ {a a'} → (R a a') ≃ (S a a')) → (A / R) ≃ (A / S)
relEquiv→QuotIdEquiv rel-equiv = isoToEquiv (relIso→QuotIdIso (equivToIso rel-equiv))

SetTruncSetQuotientPathIso : Iso ∥ A ∥₂ (A / _≡_)
SetTruncSetQuotientPathIso .Iso.fun = ST.rec SQ.squash/ SQ.[_]
SetTruncSetQuotientPathIso .Iso.inv = SQ.rec ST.isSetSetTrunc ∣_∣₂ λ a b → cong ∣_∣₂
SetTruncSetQuotientPathIso .Iso.rightInv = SQ.elimProp (λ x → SQ.squash/ _ x) λ _ → refl
SetTruncSetQuotientPathIso .Iso.leftInv = ST.elim (λ _ → isProp→isSet (ST.isSetSetTrunc _ _)) λ _ → refl

SetTrunc→SetQuotientPath : ∥ A ∥₂ → (A / _≡_)
SetTrunc→SetQuotientPath = ST.rec SQ.squash/ SQ.[_]

SetTrunc≃SetQuotientPath : ∥ A ∥₂ ≃ (A / _≡_)
SetTrunc≃SetQuotientPath = isoToEquiv SetTruncSetQuotientPathIso
-- SetTrunc≃SetQuotientPath : ∥ A ∥₂ ≃ (A / _≡_)
-- SetTrunc≃SetQuotientPath .fst = SetTrunc→SetQuotientPath
-- SetTrunc≃SetQuotientPath {A} .snd .equiv-proof = SQ.elimProp (λ _ → isPropIsContr) goal where
--   lemma : ∀ a (x y : ∥ A ∥₂) (p : SetTrunc→SetQuotientPath x ≡ SQ.[ a ]) (q : SetTrunc→SetQuotientPath y ≡ SQ.[ a ]) → Path (fiber SetTrunc→SetQuotientPath SQ.[ a ]) (x , p) (y , q)
--   lemma a = ST.elim2 (λ x y → isSetΠ2 λ p q → isProp→isSet (isSetΣSndProp ST.isSetSetTrunc (λ x → SQ.squash/ _ _) (x , p) (y , q)))
--     λ (b b′ : A) (p : SQ.[ b ] ≡ SQ.[ a ]) (q : SQ.[ b′ ] ≡ SQ.[ a ]) → ΣPathP ({! !} , {! !})

--   is-prop-fiber : ∀ a → isProp (fiber SetTrunc→SetQuotientPath SQ.[ a ])
--   is-prop-fiber a (x , p) (y , q) = lemma a x y p q
--   goal : ∀ a → isContr (fiber SetTrunc→SetQuotientPath SQ.[ a ])
--   goal a = inhProp→isContr
--     (∣ a ∣₂ , refl)
--     (is-prop-fiber a)
