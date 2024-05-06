module GpdCont.Prelude where

open import GpdCont.RecordEquiv public

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function
  using (const ; _∘_ ; _$_ ; curry ; uncurry)
  renaming (idfun to id)
  public
open import Cubical.Foundations.Structure public using (⟨_⟩ ; str)
open import Cubical.Foundations.Equiv using (_≃_ ; _≃⟨_⟩_) renaming (_■ to _≃∎) public

open import Cubical.Data.Nat.Base using (zero ; suc) public
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Sigma.Base using (∃-syntax) public

module _ where
  private
    variable
      ℓ : Level
      A B C : Type ℓ

  infixr 9 _⋆_
  _⋆_ : (f : A → B) (g : B → C) → A → C
  (f ⋆ g) x = g (f x)
  {-# INLINE _⋆_ #-}

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

ℓ-of : ∀ {ℓ} {A : Type ℓ} (a : A) → Level
ℓ-of {ℓ} _ = ℓ

open LevelNumber public

private
  variable
    ℓ : Level
    A : Type ℓ
    x y z : A

compSquareFiller : (p : x ≡ y) (q : y ≡ z) (p∙q : x ≡ z) → Type _
compSquareFiller {x} p q p∙q = PathP (λ i → x ≡ q i) p p∙q

pathComp→compSquareFiller : (p : x ≡ y) (q : y ≡ z) → compSquareFiller p q (p ∙ q)
pathComp→compSquareFiller = compPath-filler

isPropCompSquareFiller : ∀ (p : x ≡ y) (q : y ≡ z) → isProp (Σ[ r ∈ x ≡ z ] compSquareFiller p q r)
isPropCompSquareFiller p q = compPath-unique refl p q

isContrCompSquareFiller : ∀ (p : x ≡ y) (q : y ≡ z) → isContr (Σ[ r ∈ x ≡ z ] compSquareFiller p q r)
isContrCompSquareFiller p q .fst = p ∙ q , pathComp→compSquareFiller p q
isContrCompSquareFiller p q .snd = isPropCompSquareFiller p q _

coerceCompSquareFiller : {p : x ≡ y} {q : y ≡ z} {r : x ≡ z}
  → (H : p ∙ q ≡ r)
  → compSquareFiller p q r
coerceCompSquareFiller {p} {q} H = subst (compSquareFiller p q) H $ pathComp→compSquareFiller p q

compSquarePFiller : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB}
  → ∀ {x y z : A} {p : x ≡ y} {q : y ≡ z} {p∙q : x ≡ z}
  → (sq : compSquareFiller p q p∙q)
  → (sec : (a : A) → B a)
  → (sec-path : ∀ {x y : A} → (p : x ≡ y) → PathP (λ i → B (p i)) (sec x) (sec y))
  → Type ℓB
compSquarePFiller {B} {x} {p} {q} {p∙q} sq sec sec-path = SquareP (λ i j → B (sq i j)) (sec-path p) (sec-path p∙q) (refl {x = sec x}) (sec-path q)
