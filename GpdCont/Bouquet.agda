module GpdCont.Bouquet where

open import GpdCont.Prelude

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Cubes.HLevels
open import Cubical.Data.Nat.Base using (zero ; suc)
open import Cubical.HITs.Bouquet as Bq using (Bouquet)
open import Cubical.HITs.Truncation as Tr using (∥_∥_ ; ∣_∣ₕ)
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level
    A : Type ℓ

  isEquivTrunc→isOfHLevel : (n : HLevel) → isEquiv (∣_∣ₕ {A = A} {n = n}) → isOfHLevel n A
  isEquivTrunc→isOfHLevel {A} n is-equiv-trunc = isOfHLevelRespectEquiv n (invEquiv trunc-equiv) (Tr.isOfHLevelTrunc n) where
    trunc-equiv : A ≃ ∥ A ∥ n
    trunc-equiv = _ , is-equiv-trunc

  EquivTrunc→isOfHLevel : (n : HLevel) → (∥ A ∥ n ≃ A) → isOfHLevel n A
  EquivTrunc→isOfHLevel {A} n trunc-equiv = isOfHLevelRespectEquiv n trunc-equiv (Tr.isOfHLevelTrunc n)

encodeDecode : (x : Bouquet A) → (g : Bq.code x) → Bq.encode x (Bq.decode x g) ≡ g
encodeDecode x g = {! !}

-- BouquetTruncEquiv : (n : HLevel) → ∥ Bouquet A ∥ (suc n) ≃ ∥ A ∥ n
-- BouquetTruncEquiv {A} zero = isContr→Equiv (inhProp→isContr Tr.∣ Bq.base ∣ₕ (Tr.isOfHLevelTrunc {A = Bouquet A} 1)) (Tr.isOfHLevelTrunc {A = A} 0)
-- BouquetTruncEquiv (suc n) = {! Tr.PathIdTruncIso (suc n)!}
--
BouquetTruncEquiv : (n : HLevel) → ∥ Bouquet A ∥ (suc n) ≃ Bouquet (∥ A ∥ n)
BouquetTruncEquiv n = {! !}

elimPropBouquet : ∀ {ℓB} {B : Bouquet A → Type ℓB}
  → (is-prop : ∀ x → isProp (B x))
  → (base* : B Bq.base)
  → (x : Bouquet A) → B x
elimPropBouquet is-prop base* Bq.base = base*
elimPropBouquet is-prop base* (Bq.loop x i) = isProp→PathP (λ i → is-prop (Bq.loop x i)) base* base* i

isPathConnectedBouquet : isConnected 2 (Bouquet A)
isPathConnectedBouquet .fst = ∣ Bq.base ∣ₕ
isPathConnectedBouquet .snd = Tr.elim (λ _ → isOfHLevelPath 1 (is-set-tr _ _)) (elimPropBouquet (λ _ → is-set-tr _ _) refl) where
  is-set-tr : isSet (∥ Bouquet A ∥ 2)
  is-set-tr = (Tr.isOfHLevelTrunc 2)

isConnectedSucBouqet : (k : HLevel) → isConnected k A → isConnected (suc k) (Bouquet A)
isConnectedSucBouqet 0 _ = isConnectedSubtr 1 1 isPathConnectedBouquet
isConnectedSucBouqet 1 _ = isPathConnectedBouquet
isConnectedSucBouqet (suc (suc k)) conn-A = {! !}

isOfHLevelSucBouqet : (n : HLevel) → isOfHLevel n A → isOfHLevel (suc n) (Bouquet A)
isOfHLevelSucBouqet = {! !}
-- isOfHLevelSucBouqet {A} n lvl-A = isOfHLevelRespectEquiv (suc n) {!invEquiv equiv !} {! !} where
--   equiv : ∥ Bouquet A ∥ suc n ≃ A
--   equiv = BouquetTruncEquiv n ∙ₑ Tr.truncIdempotent≃ n lvl-A

-- data [_]Bouquet (n : HLevel) (A : Type ℓ) : Type ℓ where
--   base : [ n ]Bouquet A
--   loop : (a : A) → base ≡ base
--   trunc : isCubeFilled (suc n) ([ n ]Bouquet A)
--   -- trunc : isOfHLevel n ([ n ]Bouquet A)
data [_]Bouquet (n : HLevel) (A : Type ℓ) : Type ℓ where
  base : [ n ]Bouquet A
  loop : (a : A) → base ≡ base
  trunc : {! isCubeFilled (suc n) ([ n ]Bouquet A) !}
