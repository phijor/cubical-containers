module GpdCont.Polynomial where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma.Properties
open import Cubical.Reflection.StrictEquiv

record Polynomial {ℓ} (S : Type ℓ) (P : S → Type ℓ) (X : Type ℓ) : Type ℓ where
  constructor poly⟨_,_⟩
  field
    shape : S
    label : P shape → X

unquoteDecl PolynomialIsoΣ = declareRecordIsoΣ PolynomialIsoΣ (quote Polynomial)

instance
  PolynomialToΣ : ∀ {ℓ} {S : Type ℓ} {P : S → Type ℓ} {X : Type ℓ} → RecordToΣ (Polynomial S P X)
  PolynomialToΣ = toΣ PolynomialIsoΣ

private
  variable
    ℓ : Level
    S X : Type ℓ
    P : S → Type ℓ

-- record isPolynomialOfHLevel (n : HLevel) (p : Polynomial {ℓ} S P X) : Type (ℓ-of p) where
--   private
--     module p = Polynomial p
--   field
--     is-of-hlevel-shape : isOfHLevel n S
--     is-of-hlevel-label : isOfHLevel n X

-- unquoteDecl isPolynomialOfHLevelIsoΣ = declareRecordIsoΣ isPolynomialOfHLevelIsoΣ (quote isPolynomialOfHLevel)

-- instance
--   isPolynomialOfHLevelToΣ : ∀ {ℓ} {S : Type ℓ} {P : S → Type ℓ} {X : Type ℓ} {n : HLevel} {p : Polynomial S P X} → RecordToΣ (isPolynomialOfHLevel n p)
--   isPolynomialOfHLevelToΣ = toΣ isPolynomialOfHLevelIsoΣ

-- private
--   variable
--     p : Polynomial S P X

-- opaque
--   isPropIsPolynomialOfHLevel : (n : HLevel) → isProp (isPolynomialOfHLevel n p)
--   isPropIsPolynomialOfHLevel n = recordIsOfHLevel 1 (isProp× (isPropIsOfHLevel n) (isPropIsOfHLevel n))

-- PolynomialOfHLevel : (n : HLevel) (S : Type ℓ) (P : S → Type ℓ) (X : Type ℓ) → Type ℓ
-- PolynomialOfHLevel n S P X = Σ (Polynomial S P X) (isPolynomialOfHLevel n)

-- GroupoidPolynomial : (S : Type ℓ) (P : S → Type ℓ) (X : Type ℓ) → Type ℓ
-- GroupoidPolynomial = PolynomialOfHLevel 3

opaque
  isOfHLevelPolynomial : (n : HLevel)
    → isOfHLevel n S
    → isOfHLevel n X
    → isOfHLevel n (Polynomial S P X)
  isOfHLevelPolynomial n is-of-lvl-S is-of-hlevel-X = recordIsOfHLevel n $
    isOfHLevelΣ n is-of-lvl-S λ s → isOfHLevelΠ n λ _ → is-of-hlevel-X

open Polynomial

Polynomial≡ : ∀ {p q : Polynomial S P X}
  → (shape-path : p .shape ≡ q .shape)
  → (label-path : PathP (λ i → P (shape-path i) → X) (p .label) (q .label))
  → p ≡ q
Polynomial≡ shape-path label-path i .shape = shape-path i
Polynomial≡ shape-path label-path i .label = label-path i

module _ {ℓ} {S X : Type ℓ} {P : S → Type ℓ} {p q : Polynomial S P X} where
  Polynomial≡Iso : Iso (p ≡ q) (Σ[ shape-path ∈ p .shape ≡ q .shape ] PathP (λ i → P (shape-path i) → X) (p .label) (q .label))
  Polynomial≡Iso .Iso.fun path .fst = cong shape path
  Polynomial≡Iso .Iso.fun path .snd = cong label path
  Polynomial≡Iso .Iso.inv = uncurry Polynomial≡
  Polynomial≡Iso .Iso.rightInv _ = refl
  Polynomial≡Iso .Iso.leftInv _ = refl

  Polynomial≡Equiv : (p ≡ q) ≃ (Σ[ shape-path ∈ p .shape ≡ q .shape ] PathP (λ i → P (shape-path i) → X) (p .label) (q .label))
  unquoteDef Polynomial≡Equiv = defStrictIsoToEquiv Polynomial≡Equiv Polynomial≡Iso

module Map {ℓ} (S : Type ℓ) (P : S → Type ℓ) where
  map : ∀ {X Y : Type ℓ} → (f : X → Y) → Polynomial S P X → Polynomial S P Y
  map f p .shape = p .shape
  map f p .label = f ∘ p .label

  map-id : (X : Type ℓ) → map (id X) ≡ id (Polynomial S P X)
  map-id X = refl

  map-comp : ∀ {X Y Z : Type ℓ} → (f : X → Y) (g : Y → Z)
    → map (g ∘ f) ≡ map g ∘ map f
  map-comp f g = refl

open module Map' {ℓ} {S : Type ℓ} {P : S → Type ℓ} = Map S P public

-- opaque
--   isOfHLevelPolynomialOfHLevel : (n : HLevel) → isOfHLevel (suc n) (PolynomialOfHLevel (suc n) S P X)
--   isOfHLevelPolynomialOfHLevel {S} zero (p , p-lvl) (q , q-lvl) = ΣPathP (poly-path , isProp→PathP (λ i → isPropIsPolynomialOfHLevel 1) p-lvl q-lvl) where
--     open isPolynomialOfHLevel p-lvl renaming (is-of-hlevel-shape to is-prop-S ; is-of-hlevel-label to is-prop-X)

--     poly-path : p ≡ q
--     poly-path = isOfHLevelPolynomial 1 is-prop-S is-prop-X p q

--   isOfHLevelPolynomialOfHLevel {S} {P} {X} (suc n) (p , p-lvl) (q , q-lvl) = isOfHLevelΣ (suc (suc n)) is-of-lvl-poly is-of-lvl-is-poly-of-hlevel _ _ where
--     open isPolynomialOfHLevel p-lvl using (is-of-hlevel-shape ; is-of-hlevel-label)
--     is-of-lvl-poly : isOfHLevel (suc (suc n)) (Polynomial S P X)
--     is-of-lvl-poly = isOfHLevelPolynomial (suc (suc n)) is-of-hlevel-shape is-of-hlevel-label

--     is-of-lvl-is-poly-of-hlevel : (p : Polynomial S P X) → isOfHLevel (suc (suc n)) (isPolynomialOfHLevel (suc (suc n)) p)
--     is-of-lvl-is-poly-of-hlevel p = isProp→isOfHLevelSuc (suc n) (isPropIsPolynomialOfHLevel (suc (suc n)))
