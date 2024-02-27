module GpdCont.Prelude where

open import GpdCont.RecordEquiv public

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function
  using (const ; _∘_ ; _$_ ; curry ; uncurry)
  renaming (idfun to id)
  public
open import Cubical.Foundations.Structure public using (⟨_⟩ ; str)
open import Cubical.Foundations.Equiv using (_≃_) renaming (_■ to _≃∎) public

open import Cubical.Data.Nat.Literals public

module _ where
  infixr 0 _≃⟨⟩_
  _≃⟨⟩_ : ∀ {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'} → A ≃ B → A ≃ B
  A ≃⟨⟩ e = e

module LevelNumber where
  open import Agda.Builtin.Nat
  open import Agda.Builtin.Unit
  open import Agda.Builtin.FromNat public

  ℓ# : (n : Nat) → Level
  ℓ# zero = ℓ-zero
  ℓ# (suc n) = ℓ-suc (ℓ# n)

  instance
    NumberLevel : Number Level
    NumberLevel .Number.Constraint n = ⊤
    NumberLevel .Number.fromNat n = ℓ# n

open LevelNumber public

compSquareFiller : ∀ {ℓ} {A : Type ℓ} {x y z : A} → (p : x ≡ y) (q : y ≡ z) (p∙q : x ≡ z) → Type ℓ
compSquareFiller {x} p q p∙q = PathP (λ i → x ≡ q i) p p∙q

compSquarePFiller : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB}
  → ∀ {x y z : A} {p : x ≡ y} {q : y ≡ z} {p∙q : x ≡ z}
  → (sq : compSquareFiller p q p∙q)
  → (sec : (a : A) → B a)
  → (sec-path : ∀ {x y : A} → (p : x ≡ y) → PathP (λ i → B (p i)) (sec x) (sec y))
  → Type ℓB
compSquarePFiller {B} {x} {p} {q} {p∙q} sq sec sec-path = SquareP (λ i j → B (sq i j)) (sec-path p) (sec-path p∙q) (refl {x = sec x}) (sec-path q)
