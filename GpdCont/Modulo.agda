module GpdCont.Modulo where

open import GpdCont.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws as GL using ()
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path as Path using ()
open import Cubical.Foundations.Transport using (transport⁻)
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv using (funExtDep)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Nat as Nat using (ℕ)
open import Cubical.Data.Sigma as Sigma using (_×_)
open import Cubical.Data.Vec as Vec using (Vec ; [] ; _∷_)
open import Cubical.Data.Int as Int using (ℤ)

open import Cubical.HITs.Modulo public
open Nat using (_+_)

elimProp : ∀ k {ℓ} {P : Modulo k → Type ℓ} → (∀ x → isProp (P x)) → (embed* : ∀ n → P (embed n)) → ∀ x → P x
elimProp zero _ embed* (embed n) = embed* n
elimProp (suc k) is-prop-P embed* (embed n) = embed* n
elimProp (suc k) is-prop-P embed* (step n i) = isProp→PathP (λ i → is-prop-P (step n i)) (embed* n) (embed* (suc (k + n))) i

Fin : (k : ℕ) → Type
Fin zero = ⊥
Fin (suc k) = Modulo (suc k)

isSetFin : ∀ {k} → isSet (Fin k)
isSetFin {k = zero} ()
isSetFin {k = suc k} = isSetModulo

suc-mod : ∀ {k} → Modulo k → Modulo k
suc-mod (embed n) = embed (suc n)
suc-mod {k} (step n i) = path i where
  path : embed (suc n) ≡ embed (suc (k + n))
  path = ztep (suc n) ∙ cong embed (Nat.+-suc k n)

shift-mod : ∀ {k} → Modulo k → Modulo k
shift-mod = suc-mod

unshift-mod-suc : ∀ k → Modulo (suc k) → Modulo (suc k)
unshift-mod-suc k (embed n) = embed (k + n)
unshift-mod-suc k (step n i) = path i where
  path : embed (k + n) ≡ embed (k + suc (k + n))
  path = ztep {suc k} (k + n) ∙ cong embed (sym (Nat.+-suc k (k + n)))

unshift-mod : ∀ {k} → Modulo k → Modulo k
unshift-mod {k = zero} (embed n) = embed n
unshift-mod {k = suc k} = unshift-mod-suc k

shift : ∀ {k} → Fin k → Fin k
shift {k = zero} ()
shift {k = suc k} = shift-mod

unshift : ∀ {k} → Fin k → Fin k
unshift {k = zero} ()
unshift {k = suc k} = unshift-mod-suc k

shiftIso : ∀ k → Iso (Fin k) (Fin k)
shiftIso k .Iso.fun = shift
shiftIso k .Iso.inv = unshift
shiftIso zero .Iso.rightInv ()
shiftIso (suc k) .Iso.rightInv = elimProp (suc k) (λ _ → isSetModulo _ _) λ n → sym (step n)
shiftIso zero .Iso.leftInv ()
shiftIso (suc k) .Iso.leftInv = elimProp (suc k) (λ _ → isSetModulo _ _) λ n → cong embed (Nat.+-suc k n) ∙ sym (ztep {suc k} n)

shiftEquiv : ∀ k → Fin k ≃ Fin k
shiftEquiv k = isoToEquiv $ shiftIso k

shiftPath : ∀ k → Fin k ≡ Fin k
shiftPath k = ua $ shiftEquiv k

shiftPathβ : ∀ k → transport (shiftPath k) ≡ shift {k = k}
shiftPathβ k i x = uaβ (shiftEquiv k) x i
