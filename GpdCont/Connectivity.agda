module GpdCont.Connectivity where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Surjection using (isSurjection ; isPropIsSurjection)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties as Nat using ()
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties as Sigma using ()
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.Truncation as Tr using (∥_∥_)
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level
    A B : Type ℓ
    f : A → B

isPathConnected : (A : Type ℓ) → Type ℓ
isPathConnected A = isContr ∥ A ∥₂

isPathConnectedFun : (f : A → B) → Type _
isPathConnectedFun {B} f = (b : B) →  isPathConnected (fiber f b)

isPropIsConnected : ∀ {n : HLevel} → isProp (isConnected n A)
isPropIsConnected = isPropIsContr

isPropIsConnectedFun : ∀ {n : HLevel} {f : A → B} → isProp (isConnectedFun n f)
isPropIsConnectedFun = isPropΠ λ _ → isPropIsConnected

merelyInh≃is1Connected : ∥ A ∥₁ ≃ isConnected 1 A
merelyInh≃is1Connected {A} =
  ∥ A ∥₁ ≃⟨ Tr.propTrunc≃Trunc1 ⟩
  ∥ A ∥ 1 ≃⟨ invEquiv $ Sigma.Σ-contractSnd (λ p → isContrΠ λ q → isProp→isContrPath (Tr.isOfHLevelTrunc 1) p q) ⟩
  isConnected 1 A ≃∎

isConnectedSuc→merelyInh : ∀ (k : HLevel) → isConnected (suc k) A → ∥ A ∥₁
isConnectedSuc→merelyInh {A} k conn-A = Tr.propTruncTrunc1Iso .Iso.inv (isConnectedSubtr 1 k conn-A' .fst) where
  conn-A' : isConnected (k + 1) A
  conn-A' = subst (λ ⌜·⌝ → isConnected ⌜·⌝ A) (Nat.+-comm 1 k) conn-A

isSurjection≃is1ConnectedFun : (f : A → B) → isSurjection f ≃ isConnectedFun 1 f
isSurjection≃is1ConnectedFun f = equivΠCod λ b → merelyInh≃is1Connected

pointed×isConnectedPath→isConnectedSuc : ∀ (k : HLevel) → (a : A) → ((a b : A) → isConnected k (a ≡ b)) → isConnected (suc k) A
pointed×isConnectedPath→isConnectedSuc {A} k a conn-path = conn where
  is-of-hlevel-trunc : isOfHLevel (2 + k) (∥ A ∥ (suc k))
  is-of-hlevel-trunc = isOfHLevelSuc (1 + k) (Tr.isOfHLevelTrunc (1 + k))

  conn : isConnected (suc k) A
  conn .fst = Tr.∣ a ∣ₕ
  conn .snd = Tr.elim
    (λ y → is-of-hlevel-trunc Tr.∣ a ∣ y)
    (λ b → Tr.PathIdTruncIso k .Iso.inv (conn-path a b .fst))

merelyInh×isConnectedPath→isConnectedSuc : ∀ (k : HLevel)
  → ∥ A ∥₁
  → ((a b : A) → isConnected k (a ≡ b))
  → isConnected (suc k) A
merelyInh×isConnectedPath→isConnectedSuc k = PT.rec
  (isProp→ isPropIsConnected)
  (pointed×isConnectedPath→isConnectedSuc k)

-- A type is k+1-connected whenever it is merely inhabited and has k-connected paths.
merelyInh×isConnectedPath≃isConnectedSuc : ∀ (k : HLevel)
  → (∥ A ∥₁ × ((a b : A) → isConnected k (a ≡ b))) ≃ (isConnected (suc k) A)
merelyInh×isConnectedPath≃isConnectedSuc k = propBiimpl→Equiv
  (isProp× PT.isPropPropTrunc $ isPropΠ2 λ a b → isPropIsConnected)
  isPropIsConnected
  (uncurry $ merelyInh×isConnectedPath→isConnectedSuc k)
  λ where
    suc-conn-A .fst → isConnectedSuc→merelyInh k suc-conn-A
    suc-conn-A .snd → isConnectedPath k suc-conn-A

inhTruncSuc×isConnectedPath→isConnectedSuc : ∀ (k : HLevel)
  → ∥ A ∥ (suc k)
  → ((a b : A) → isConnected k (a ≡ b))
  → isConnected (suc k) A
inhTruncSuc×isConnectedPath→isConnectedSuc k = Tr.rec
  (isOfHLevelΠ (suc k) λ _ → isProp→isOfHLevelSuc k isPropIsConnected)
  (pointed×isConnectedPath→isConnectedSuc k)

-- A type is k+1-connected whenever it is k+1-inhabited and has k-connected paths.
--
-- Note that the left hand side of the equivalence is not a priori a proposition.
inhTruncSuc×isConnectedPath≃isConnectedSuc : ∀ (k : HLevel)
  → (∥ A ∥ (suc k) × ((a b : A) → isConnected k (a ≡ b))) ≃ (isConnected (suc k) A)
inhTruncSuc×isConnectedPath≃isConnectedSuc {A} k = equiv where
  -- The left-to-right implication has been established above.
  impl : (∥ A ∥ (suc k) × ((a b : A) → isConnected k (a ≡ b))) → (isConnected (suc k) A)
  impl = uncurry (inhTruncSuc×isConnectedPath→isConnectedSuc k)

  -- Even though ∥ A ∥ₖ₊₁ is not a proposition in general, we know that this is the
  -- case whenever A is k+1-connected.  We can thus prove that fibers of the above
  -- implication are contractible, since we get to assume k+1-connectivity of A:
  is-contr-fiber-impl : (suc-conn-A : isConnected (suc k) A) → isContr (fiber impl suc-conn-A)
  is-contr-fiber-impl suc-conn-A = isContrΣ
    is-contr-trunc×conn-path
    (λ x → isProp→isContrPath isPropIsConnected (impl x) suc-conn-A)
    where
      is-contr-is-conn-path : isContr (∀ (a b : A) → isConnected k (a ≡ b))
      is-contr-is-conn-path = inhProp→isContr (isConnectedPath k suc-conn-A) (isPropΠ2 λ _ _ → isPropIsConnected)

      is-contr-trunc×conn-path : isContr (∥ A ∥ (suc k) × ∀ (a b : A) → isConnected k (a ≡ b))
      is-contr-trunc×conn-path = isContrΣ suc-conn-A λ _ → is-contr-is-conn-path

  equiv : _ ≃ _
  equiv .fst = impl
  equiv .snd .equiv-proof = is-contr-fiber-impl

isContr→isConnected : (k : HLevel) → isContr A → isConnected k A
isContr→isConnected = Tr.isContr→isContrTrunc

-- A k-connected k-type is contractible.
isOfHLevel×isConnected→isContr : (k : HLevel)
  → (A : Type ℓ)
  → (isOfHLevel k A)
  → (isConnected k A)
  → isContr A
isOfHLevel×isConnected→isContr zero A is-contr-A _ = is-contr-A
isOfHLevel×isConnected→isContr (suc k) A suc-k-level-A suc-k-conn-A = is-contr-A where
  universal-property-trunc : ∥ A ∥ suc k ≃ A
  universal-property-trunc = Tr.truncIdempotent≃ (suc k) suc-k-level-A

  is-contr-A : isContr A
  is-contr-A = isOfHLevelRespectEquiv 0 universal-property-trunc suc-k-conn-A
