module GpdCont.FinOrd where

open import GpdCont.Prelude
open import GpdCont.Equiv
open import GpdCont.Univalence
open import GpdCont.SetQuotients as SQ

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Foundations.Structure
open import Cubical.Functions.Fibration using (totalEquiv)
open import Cubical.Data.Empty as Empty using (⊥)
import      Cubical.Data.Fin.Recursive as FinR
open import Cubical.Data.FinSet as FinSet using (isFinOrd) public
import      Cubical.Data.FinSet.Constructors as FinSet
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin as Fin using (totalSum)
open import Cubical.HITs.SetQuotients as SQ

Fin : ℕ → hSet _
Fin n .fst = Fin.Fin n
Fin n .snd = Fin.isSetFin {n}

FinOrd : Type₁
FinOrd = TypeWithStr ℓ-zero isFinOrd

card : FinOrd → ℕ
card (X , n , _) = n

to-fin : (X : FinOrd) → ⟨ X ⟩ ≃ ⟨ Fin (card X) ⟩
to-fin (X , _ , α) = α

opaque
  isFinOrd→isSet : (X : Type) → isFinOrd X → isSet X
  isFinOrd→isSet X (n , α) = isOfHLevelRespectEquiv 2 (invEquiv α) (str $ Fin n)

FinOrd→hSet : FinOrd → hSet _
FinOrd→hSet (X , ord) .fst = X
FinOrd→hSet (X , ord) .snd = isFinOrd→isSet X ord

isFinOrdRespectEquiv : ∀ {X Y : Type}
  → Y ≃ X
  → isFinOrd X
  → isFinOrd Y
isFinOrdRespectEquiv e (n , α) .fst = n
isFinOrdRespectEquiv e (n , α) .snd = e ∙ₑ α

FinOrdΣ : (X : FinOrd) → (Y : ⟨ X ⟩ → FinOrd) → FinOrd
FinOrdΣ X Y .fst = Σ[ x ∈ ⟨ X ⟩ ] ⟨ Y x ⟩
FinOrdΣ X Y .snd = FinSet.isFinOrdΣ ⟨ X ⟩ (str X) (⟨_⟩ ∘ Y) (str ∘ Y)

ℕ≃FinOrd : ℕ ≃ FinOrd
ℕ≃FinOrd = totalEquiv Fin.Fin ∙ₑ Σ-cong-equiv-snd λ X → Σ-cong-equiv-snd λ n → symEquiv ∙ₑ univalence

opaque
  isSetFinOrd : isSet FinOrd
  isSetFinOrd = isOfHLevelRespectEquiv 2 ℕ≃FinOrd isSetℕ

cardEquiv : FinOrd ≃ ℕ
cardEquiv = invEquiv ℕ≃FinOrd

isEquivCard : isEquiv card
isEquivCard = equivIsEquiv cardEquiv

FinOrdPathEquiv : ∀ {X Y : FinOrd} → (X ≡ Y) ≃ (card X ≡ card Y)
FinOrdPathEquiv = congEquiv cardEquiv

FinOrd≡' : ∀ {X Y : FinOrd} → card X ≡ card Y → X ≡ Y
FinOrd≡' = invEq FinOrdPathEquiv

FinOrd≡ : ∀ {X Y : FinOrd} → card X ≡ card Y → X ≡ Y
FinOrd≡ {X = X , n , α} {Y = Y , m , β} p = ΣPathP λ where
    .fst → ua $ α ∙ₑ pathToEquiv (cong Fin.Fin p) ∙ₑ invEquiv β
    .snd → ΣPathP λ where
      .fst → p
      .snd → equivPathP $ ua→ λ x → toPathP $ coh x
  where
    γ : (a : X) → Fin.Fin m
    γ = subst Fin.Fin p ∘ equivFun α

    coh : (x : X) → γ x ≡ equivFun β (invEq β (γ x))
    coh x = sym (secEq β (γ x))

FinOrd≡-β : ∀ (X Y : FinOrd) {p : card X ≡ card Y} → transport (cong ⟨_⟩ $ FinOrd≡ {X} {Y} p) ≡ (invEq (to-fin Y) ∘ subst Fin.Fin p ∘ equivFun (to-fin X))
FinOrd≡-β (X , n , α) (Y , m , β) {p} = funExt λ _ → transportRefl _

-- Idea: Do by injectivity of Fin and sum-Fin-equiv
totalSum-permute-snd : ∀ {n} (f f' : ⟨ Fin n ⟩ → ℕ)
  → (π : ⟨ Fin n ⟩ ≃ ⟨ Fin n ⟩)
  → (p : f ≡ f' ∘ equivFun π)
  → ⟨ Fin (totalSum {n} f) ⟩ ≃ ⟨ Fin (totalSum {n} f') ⟩
totalSum-permute-snd {n} f f' π p =
  ⟨ Fin (totalSum {n} f) ⟩
    ≃⟨ invEquiv (Fin.SumFinΣ≃ n f) ⟩
  (Σ[ k ∈ ⟨ Fin n ⟩ ] ⟨ Fin (f k) ⟩ )
    ≃⟨ Σ-cong-equiv π (λ k → substEquiv (λ - → ⟨ Fin - ⟩) (p ≡$ k)) ⟩
  (Σ[ k ∈ ⟨ Fin n ⟩ ] ⟨ Fin (f' k) ⟩ )
    ≃⟨ Fin.SumFinΣ≃ n f' ⟩
  ⟨ Fin (totalSum {n} f') ⟩
    ≃∎

opaque
  Fin-inj : ∀ {n m} → ⟨ Fin n ⟩ ≃ ⟨ Fin m ⟩ → n ≡ m
  Fin-inj e = FinR.Fin-inj _ _ $ ua $ (invEquiv convert-equiv) ∙ₑ e ∙ₑ convert-equiv where
    to : ∀ {n} → ⟨ Fin n ⟩ → FinR.Fin n
    to {n = suc n} Fin.fzero = FinR.zero
    to {n = suc n} (Fin.fsuc k) = FinR.suc $ to k

    from : ∀ {n} → FinR.Fin n → ⟨ Fin n ⟩
    from {n = suc n} FinR.zero = Fin.fzero
    from {n = suc n} (FinR.suc k) = Fin.fsuc $ from k

    rinv : ∀ {n} → section (to {n}) from
    rinv {suc n} FinR.zero = refl
    rinv {suc n} (FinR.suc k) = cong FinR.suc (rinv k)

    linv : ∀ {n} → retract (to {n}) from
    linv {suc n} Fin.fzero = refl
    linv {suc n} (Fin.fsuc k) = cong Fin.fsuc (linv k)

    convert : ∀ {n} → Iso ⟨ Fin n ⟩ (FinR.Fin n)
    convert .Iso.fun = to
    convert .Iso.inv = from
    convert .Iso.rightInv = rinv
    convert .Iso.leftInv = linv

    convert-equiv : ∀ {n} → ⟨ Fin n ⟩ ≃ (FinR.Fin n)
    convert-equiv = isoToEquiv convert

    convert-path : ∀ {n} → ⟨ Fin n ⟩ ≡ (FinR.Fin n)
    convert-path = isoToPath convert

setQuotientDepChoiceIso : ∀ {ℓ ℓR} (A : FinOrd)
  → (B : ⟨ A ⟩ → Type ℓ)
  → (R : ∀ a → B a → B a → Type ℓR)
  → Iso ((∀ a → B a) / λ f g → ∀ a → R a (f a) (g a)) (∀ a → B a / R a)
setQuotientDepChoiceIso A B R .Iso.fun = SQ.rec {! !} (λ f a → [ f a ]) λ f g r → funExt λ a → SQ.eq/ _ _ (r a)
setQuotientDepChoiceIso A B R .Iso.inv = {!SQ.rec !}
setQuotientDepChoiceIso A B R .Iso.rightInv = {! !}
setQuotientDepChoiceIso A B R .Iso.leftInv = {! !}

setQuotientChoiceIso' : ∀ {ℓ ℓR}
  → (B : Type ℓ)
  → (R : B → B → Type ℓR)
  → (n : ℕ)
  → Iso ((⟨ Fin n ⟩ → B) / λ f g → ∀ a → R (f a) (g a)) (⟨ Fin n ⟩ → B / R)
setQuotientChoiceIso' B R = Nat.elim go₀ go-suc where
  go₀ : Iso ((⊥ → B) / _) (⊥ → B / R)
  go₀ .Iso.fun _ ()
  go₀ .Iso.inv _ = [ (λ ()) ]
  go₀ .Iso.rightInv _ = funExt λ ()
  go₀ .Iso.leftInv = elimProp (λ f → SQ.squash/ _ _) λ f → cong [_] $ funExt λ ()

  go-suc : (n : ℕ) → Iso _ _ → Iso _ _
  go-suc n choose-iso .Iso.fun f k = map (_$ k) (λ r → r k) f
  -- go-suc n choose-iso .Iso.fun f (Fin.fzero) = map (_$ Fin.fzero) (λ r → r Fin.fzero) f
  -- go-suc n choose-iso .Iso.fun f (Fin.fsuc k) = map (_$ Fin.fsuc k) (λ r → r _) f
  go-suc n choose-iso .Iso.inv f = [ Fin.elim (λ _ → B) {! (f Fin.fzero)!} {! !} ] where
    f' = choose-iso .Iso.inv (f ∘ Fin.fsuc)
  go-suc n choose-iso .Iso.rightInv = {! !}
  go-suc n choose-iso .Iso.leftInv = {! !}
    -- ((⟨ Fin (suc n) ⟩ → B) / _)
    --   Iso⟨ pullbackQuotIso $ {! !} ⟩
    -- ((B × (⟨ Fin n ⟩ → B)) / _)
    --   Iso⟨ {! !} ⟩
    -- (⟨ Fin (suc n) ⟩ → (B / _))
    --   Iso∎

setQuotientChoiceIso : ∀ {ℓ ℓR} (A : FinOrd)
  → (B : Type ℓ)
  → (R : B → B → Type ℓR)
  → Iso ((⟨ A ⟩ → B) / λ f g → ∀ a → R (f a) (g a)) (⟨ A ⟩ → B / R)
setQuotientChoiceIso A B R .Iso.fun = SQ.rec (isSet→ SQ.squash/) (λ f a → [ f a ]) λ f g r → funExt λ a → SQ.eq/ _ _ (r a)
setQuotientChoiceIso A B R .Iso.inv f/ = {! !}
setQuotientChoiceIso A B R .Iso.rightInv = {! !}
setQuotientChoiceIso A B R .Iso.leftInv = {! !}
