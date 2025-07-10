open import Cubical.Foundations.Prelude

module GpdCont.Prelude.Path {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} where

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (Π-contractDom)

yo : (x : A) → B x ≃ (∀ y → x ≡ y → B y)
yo x =
  B x ≃⟨ invEquiv (Π-contractDom (isContrSingl x)) ⟩
  (((y , _) : singl x) → B y) ≃⟨ curryEquiv ⟩
  (∀ y → x ≡ y → B y) ■

_≡[_]_ : {x y : A}
  → (xᴰ : B x)
  → (p : x ≡ y)
  → (yᴰ : B y)
  → Type _
xᴰ ≡[ p ] yᴰ = PathP (λ i → B (p i)) xᴰ yᴰ

≡in : {x y : A} {xᴰ : B x} {yᴰ : B y}
  → {p : x ≡ y}
  → (pᴰ : xᴰ ≡[ p ] yᴰ)
  → (x , xᴰ) ≡ (y , yᴰ)
≡in {p = p} pᴰ i .fst = p i
≡in {p = p} pᴰ i .snd = pᴰ i

≡out : {x y : A} {xᴰ : B x} {yᴰ : B y}
  → (q : (x , xᴰ) ≡ (y , yᴰ))
  → xᴰ ≡[ cong fst q ] yᴰ
≡out = cong snd

module _ {x y : A} (p : x ≡ y) where opaque
  reind : B x → B y
  reind = subst B p

  reind-filler : (xᴰ : B x) → (x , xᴰ) ≡ (y , reind xᴰ)
  reind-filler xᴰ = ΣPathP (p , subst-filler B p xᴰ)

rectify : isSet A → {x y : A} {p₀ p₁ : x ≡ y}
  → {xᴰ : B x} {yᴰ : B y}
  → xᴰ ≡[ p₀ ] yᴰ
  → xᴰ ≡[ p₁ ] yᴰ
rectify is-set-A {xᴰ} {yᴰ} = subst (xᴰ ≡[_] yᴰ) (is-set-A _ _ _ _)

rectify-refl : isSet A → {x : A} {p : x ≡ x}
  → {xᴰ yᴰ : B x}
  → xᴰ ≡ yᴰ
  → xᴰ ≡[ p ] yᴰ
rectify-refl is-set-A = rectify is-set-A
