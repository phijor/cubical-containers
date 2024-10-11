module GpdCont.Prelude where

open import GpdCont.RecordEquiv public

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function
  using (const ; _∘_ ; _$_ ; curry ; uncurry)
  renaming (idfun to id)
  public
open import Cubical.Foundations.Structure public using (⟨_⟩ ; str)
open import Cubical.Foundations.Equiv using (_≃_ ; _≃⟨_⟩_) renaming (_■ to _≃∎) public
open import Cubical.Foundations.Equiv using (equivFun ; invEq ; isEquiv)
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv ; preCompEquiv ; congEquiv)
open import Cubical.Foundations.Isomorphism as Isomorphism using (Iso ; _Iso⟨_⟩_) renaming (_∎Iso to _Iso∎) public
open import Cubical.Foundations.Transport as Transport using ()

open import Cubical.Data.Nat.Base using (zero ; suc) public
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Sigma.Base using (∃ ; ∃-syntax ; _×_) public

import Cubical.HITs.PropositionalTruncation as PT

module _ where
  private
    variable
      ℓ : Level
      A B C : Type ℓ

  infixr 9 _⋆_
  _⋆_ : (f : A → B) (g : B → C) → A → C
  (f ⋆ g) x = g (f x)
  {-# INLINE _⋆_ #-}

  the : (A : Type ℓ) → (a : A) → A
  the _ a = a

  refl′ : (x : A) → x ≡ x
  refl′ x i = x

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
compSquareFiller {x} p q p∙q = Square p p∙q refl q

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

compSquareFillerUnique : {p : x ≡ y} {q : y ≡ z} {r : x ≡ z}
  → compSquareFiller p q r
  → p ∙ q ≡ r
compSquareFillerUnique sq = cong fst (isContrCompSquareFiller _ _ .snd (_ , sq))

compSquarePFiller : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB}
  → ∀ {x y z : A} {p : x ≡ y} {q : y ≡ z} {p∙q : x ≡ z}
  → (sq : compSquareFiller p q p∙q)
  → (sec : (a : A) → B a)
  → (sec-path : ∀ {x y : A} → (p : x ≡ y) → PathP (λ i → B (p i)) (sec x) (sec y))
  → Type ℓB
compSquarePFiller {B} {x} {p} {q} {p∙q} sq sec sec-path = SquareP (λ i j → B (sq i j)) (sec-path p) (sec-path p∙q) (refl {x = sec x}) (sec-path q)

doubleCompPathP : ∀ {ℓ} (A : (i j : I) → Type ℓ)
  → {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
  → PathP (λ i → A i i0) a₀₀ a₁₀
  → PathP (λ j → A i0 j) a₀₀ a₀₁
  → PathP (λ i → A i i1) a₀₁ a₁₁
  → PathP (λ j → A i1 j) a₁₀ a₁₁
doubleCompPathP A p q r j = comp (λ i → A i j) {φ = j ∨ ~ j}
  (λ where
    i (j = i0) → p i
    i (j = i1) → r i
  )
  (q j)

opaque
  compPath≡Square : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
    → (p ∙ s ≡ r ∙ q) ≡ (Square r s p q)
  compPath≡Square {A} {a} {d} {p} {q} {r} {s} = goal where
    open import Cubical.Foundations.Path
    open import Cubical.Foundations.Univalence
    open import Cubical.Foundations.GroupoidLaws

    goal : (p ∙ s ≡ r ∙ q) ≡ (Square r s p q)
    goal =
      (p ∙ s ≡ r ∙ q)                     ≡⟨ ua (strictIsoToEquiv symIso) ⟩
      (r ∙ q ≡ p ∙ s)                     ≡⟨ ua (congEquiv (compPathlEquiv (sym p))) ⟩
      (sym p ∙ (r ∙ q) ≡ sym p ∙ (p ∙ s)) ≡[ i ]⟨ sym p ∙ (r ∙ q) ≡ assoc (sym p) p s i ⟩
      (sym p ∙ (r ∙ q) ≡ (sym p ∙ p) ∙ s) ≡[ i ]⟨ sym p ∙ (r ∙ q) ≡ lCancel p i ∙ s ⟩
      (sym p ∙ (r ∙ q) ≡ refl ∙ s)        ≡[ i ]⟨ sym p ∙ (r ∙ q) ≡ lUnit s (~ i) ⟩
      (sym p ∙ (r ∙ q) ≡ s)               ≡⟨ cong (_≡ s) $ sym (doubleCompPath-elim' (sym p) r q) ⟩
      (sym p ∙∙ r ∙∙ q ≡ s)               ≡⟨ sym (PathP≡doubleCompPathˡ p r s q) ⟩
      (Square r s p q) ∎

compPath≃Square : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
  → (p ∙ s ≡ r ∙ q) ≃ (Square r s p q)
compPath≃Square {p} {q} {r} {s} = pathToEquiv compPath≡Square where
  open import Cubical.Foundations.Univalence using (pathToEquiv)

substCodomain : ∀ {ℓ′ ℓ″} {x y : A} (B : A → Type ℓ′) {C : Type ℓ″} (p : x ≡ y) (f : B x → C)
  → subst (λ a → B a → C) p f ≡ f ∘ subst B (sym p)
substCodomain {A} {x} B {C} = J (λ y p → (f : B x → C) → subst (λ a → B a → C) p f ≡ f ∘ subst B (sym p)) goal
  where module _ (f : B x → C) where
    B→C = λ a → B a → C

    step₁ : subst B→C refl f ≡ f
    step₁ = substRefl {B = B→C} f

    step₂ : f ≡ f ∘ subst B refl
    step₂ = funExt λ a → cong f $ sym (substRefl {B = B} a)

    goal : subst (λ a → B a → C) refl f ≡ f ∘ subst B refl
    goal = step₁ ∙ step₂

preCompAdjointEquiv : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
  → (e : A ≃ B)
  → (f : A → C)
  → (g : B → C)
  → (g ≡ f ∘ invEq e) ≃ (g ∘ equivFun e ≡ f)
preCompAdjointEquiv e f g = equivAdjointEquiv (preCompEquiv e) {a = g} {b = f}


isProp∃ : ∀ {ℓ'} (A : Type ℓ) (B : A → Type ℓ') → isProp (∃[ a ∈ A ] B a)
isProp∃ A B = PT.isPropPropTrunc {A = Σ A B}

module _ where
  private
    variable
      ℓᴰ : Level
      A′ A″ : Type ℓ
      B : A → Type ℓᴰ
      B′ : A′ → Type ℓᴰ
      B″ : A″ → Type ℓᴰ

  ∃-intro : (a : A) (b : B a) → ∃[ a ∈ A ] B a
  ∃-intro a b = PT.∣ a , b ∣₁

  ∃-elim : ∀ {ℓP} {P : ∃ A B → Type ℓP}
    → (∀ x → isProp (P x))
    → (∀ a (b : B a) → P $ ∃-intro a b)
    → (x : ∃ A B) → P x
  ∃-elim is-prop-P f = PT.elim is-prop-P (uncurry f)

  ∃-rec : ∀ {ℓP} {P : Type ℓP} → isProp P → (∀ a → B a → P) → (∃ A B) → P
  ∃-rec is-prop-P f = PT.rec is-prop-P (uncurry f)

  ∃-map : (f : A → A′) → (g : ∀ {a} (b : B a) → B′ (f a)) → ∃ A B → ∃ A′ B′
  ∃-map f g = PT.map λ { (a , b) → f a , g b }

  ∃-map2 : (f : A → A′ → A″) (g : ∀ {a a′} → B a → B′ a′ → B″ (f a a′)) → ∃ A B → ∃ A′ B′ → ∃ A″ B″
  ∃-map2 f g = PT.map2 λ { (a , b) (a′ , b′) → f a a′ , g b b′ }
