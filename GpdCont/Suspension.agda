module GpdCont.Suspension where

open import GpdCont.Prelude
open import GpdCont.Connectivity

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.HITs.Susp as Susp using (Susp)
open import Cubical.HITs.Pushout as Pushout using (Pushout)
open import Cubical.HITs.Truncation as Tr using (∥_∥_)
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level
    A B C : Type ℓ
    f : A → B
    g : A → C

-- isOfHLevelSusp : (n : HLevel) → isOfHLevel n A → isOfHLevel n (Susp A)
-- isOfHLevelSusp n = ?
--
isProp→isSetSusp : isProp A → isSet (Susp A)
isProp→isSetSusp prop-A = {! !}

record SuspStr {ℓ} (S A : Type ℓ) : Type ℓ where
  field
    north* : S
    south* : S
    merid* : (a : A) → Path S north* south*

  map : {S′ : Type ℓ} (f : S → S′) → SuspStr S′ A
  map f .north* = f north*
  map f .south* = f south*
  map f .merid* = cong f ∘ merid*

  isUniversal : Type (ℓ-suc ℓ)
  isUniversal = ∀ (S′ : Type ℓ) → isEquiv (map {S′ = S′})

  cogap : Susp A → S
  cogap Susp.north = north*
  cogap Susp.south = south*
  cogap (Susp.merid a i) = merid* a i

  isSuspension : Type ℓ
  isSuspension = isEquiv cogap

SuspSuspStr : (A : Type ℓ) → SuspStr (Susp A) A
SuspSuspStr A .SuspStr.north* = Susp.north
SuspSuspStr A .SuspStr.south* = Susp.south
SuspSuspStr A .SuspStr.merid* = Susp.merid

Susp-map-cogap-Iso : ∀ {S : Type ℓ} → Iso (Susp A → S) (SuspStr S A)
Susp-map-cogap-Iso {A} {S} = is where
  module SuspA = SuspStr (SuspSuspStr A)

  is : Iso (Susp A → S) (SuspStr S A)
  is .Iso.fun = SuspA.map {S′ = S}
  is .Iso.inv ΣS = SuspStr.cogap ΣS
  is .Iso.rightInv ΣS = refl
  is .Iso.leftInv f i Susp.north = f Susp.north
  is .Iso.leftInv f i Susp.south = f Susp.south
  is .Iso.leftInv f i (Susp.merid a j) = f (Susp.merid a j)

isUniversalSuspSuspStr : SuspStr.isUniversal (SuspSuspStr A)
isUniversalSuspSuspStr S′ = isoToIsEquiv (Susp-map-cogap-Iso {S = S′})

SuspMapEquiv : ∀ S → (Susp A → S) ≃ SuspStr S A
SuspMapEquiv S .fst = SuspStr.map (SuspSuspStr _)
SuspMapEquiv S .snd = isUniversalSuspSuspStr S

isConnectedSucSusp : (k : HLevel) → isConnected k A → isConnected (suc k) (Susp A)
-- isConnectedSucSusp zero conn-A = {! !}
-- isConnectedSucSusp (suc k) conn-A = isContrRetract (const tt) (const (Tr.rec₊ ({!Tr.isOfHLevelTrunc (suc k)!}) {! !} (conn-A .fst))) {! !} isContrUnit
isConnectedSucSusp {A} k conn-A = indMapEquiv→conType (suc k) goal where
  module _ (B : TypeOfHLevel _ (suc k)) where
    equiv : (Susp A → ⟨ B ⟩) ≃ ⟨ B ⟩
    equiv =
      (Susp A → ⟨ B ⟩) ≃⟨ SuspMapEquiv ⟨ B ⟩ ⟩
      (SuspStr ⟨ B ⟩ A) ≃⟨ {! !} ⟩
      ⟨ B ⟩ ≃∎

    is : Iso ⟨ B ⟩ (Susp A → ⟨ B ⟩)
    is .Iso.fun b _ = b
    is .Iso.inv = {! !}
    is .Iso.rightInv = {! !}
    is .Iso.leftInv = {! !}
    goal : isEquiv (λ (b : ⟨ B ⟩) → λ (_ : Susp A) → b)
    goal = isoToIsEquiv is

-- record isPushoutOf {ℓ} {A B C : Type ℓ} (f : A → B) (g : A → C) (P : Type ℓ) : Type (ℓ-suc ℓ) where
--   field
--     inl : B → P
--     inr : C → P
--     push : ∀ (a : A) → inl (f a) ≡ inr (g a)

--   Rec : ∀ (E : Type ℓ) → Type ℓ
--   Rec E = Σ[ inl* ∈ (B → E) ] Σ[ inr* ∈ (C → E) ] (∀ a → inl* (f a) ≡ inr* (g a))

--   rec⁻ : ∀ {E : Type ℓ} → (P → E) → Rec E
--   rec⁻ f = f ∘ inl , f ∘ inr , cong f ∘ push

--   field
--     is-pushout : ∀ {E : Type ℓ} → isEquiv (rec⁻ {E = E})

-- isPushoutOf→PushoutEquiv : ∀ {f : A → B} {g : A → C} (P : Type ℓ) → isPushoutOf f g P → Pushout f g ≃ P
-- isPushoutOf→PushoutEquiv {f} {g} P is-pushout-of-fg = equiv where
--   module P = isPushoutOf is-pushout-of-fg

--   to-P : Pushout f g → P
--   to-P (Pushout.inl a) = P.inl a
--   to-P (Pushout.inr b) = P.inr b
--   to-P (Pushout.push a i) = P.push a i

--   equiv : _ ≃ _
--   equiv .fst = {!P.is-pushout !}
--   equiv .snd = {! !}
