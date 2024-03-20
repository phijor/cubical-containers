module GpdCont.SetTruncation where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.Data.Sigma
open import Cubical.Functions.Surjection
open import Cubical.Functions.Fibration

private
  variable
    ℓA ℓB : Level
    A : Type ℓA
    B : A → Type ℓB

IsoSetTruncateFstΣ : isSet A → Iso ∥ Σ A B ∥₂ (Σ A (∥_∥₂ ∘ B))
IsoSetTruncateFstΣ {A} {B} is-set-A = go where
  isSetΣA∥B∥ : isSet (Σ A (∥_∥₂ ∘ B))
  isSetΣA∥B∥ = isSetΣ is-set-A λ a → ST.isSetSetTrunc
  go : Iso _ _
  go .Iso.fun = ST.rec isSetΣA∥B∥ λ { (a , b) → a , ST.∣ b ∣₂ }
  go .Iso.inv = uncurry λ a → ST.rec ST.isSetSetTrunc λ { b → ST.∣ a , b ∣₂ }
  go .Iso.rightInv = uncurry λ a → ST.elim (λ ∣b∣ → isProp→isSet (isSetΣA∥B∥ _ (a , ∣b∣))) λ _ → refl
  go .Iso.leftInv = ST.elim (λ ∣a,b∣ → isProp→isSet (ST.isSetSetTrunc _ ∣a,b∣)) λ _ → refl

setTruncateFstΣ≃ : isSet A → ∥ Σ A B ∥₂ ≃ (Σ A (∥_∥₂ ∘ B))
setTruncateFstΣ≃ = isoToEquiv ∘ IsoSetTruncateFstΣ

componentEquiv : (A : Type ℓA) → A ≃ (Σ[ x ∈ ∥ A ∥₂ ] fiber ∣_∣₂ x)
componentEquiv A = totalEquiv {B = ∥ A ∥₂} {E = A} ∣_∣₂

isSurjection-∣-∣₂ : ∀ (A : Type ℓA) → isSurjection (∣_∣₂ {A = A})
isSurjection-∣-∣₂ A = (ST.elim (λ _ → isProp→isSet PT.isPropPropTrunc) λ { a → PT.∣ a , refl ∣₁ })

isConnected-fiber-∣-∣₂ : ∀ (x : ∥ A ∥₂) → isContr ∥ fiber ∣_∣₂ x ∥₂
isConnected-fiber-∣-∣₂ {A} = ST.elim (λ x → isProp→isSet isPropIsContr) contr where
  lemma : ∀ {a b : A} → (p : ∣ b ∣₂ ≡ ∣ a ∣₂) → ∣ a , refl {x = ∣ a ∣₂} ∣₂ ≡ ∣ b , p ∣₂
  lemma {a} {b} p = PT.elim {P = λ p' → ∣ a , refl ∣₂ ≡ ∣ b , p ∣₂} (λ _ → ST.squash₂ _ _)
    (λ p' → cong ∣_∣₂ (ΣPathP (sym p' , isProp→PathP (λ i → ST.squash₂ ∣ p' (~ i) ∣₂ ∣ a ∣₂) (λ _ → ∣ a ∣₂) p)))
    (ST.PathIdTrunc₀Iso .Iso.fun p)

  contr : (a : A) → isContr ∥ fiber ∣_∣₂ ∣ a ∣₂ ∥₂
  contr a .fst = ∣ a , refl {x = ∣ a ∣₂} ∣₂
  contr a .snd = ST.elim (λ ∣fib∣ → ST.isSetPathImplicit) λ { (b , p) → lemma p }
