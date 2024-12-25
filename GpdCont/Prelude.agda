module GpdCont.Prelude where

open import GpdCont.RecordEquiv public

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function
  using (const ; _∘_ ; _$_ ; curry ; uncurry ; flip)
  renaming (idfun to id)
  public
open import Cubical.Foundations.Structure public using (⟨_⟩ ; str)
open import Cubical.Foundations.Equiv using (_≃_ ; _≃⟨_⟩_) renaming (_■ to _≃∎) public
open import Cubical.Foundations.Equiv using (equivFun ; invEq ; isEquiv ; _∙ₑ_)
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv ; preCompEquiv ; congEquiv)
open import Cubical.Foundations.HLevels as HLevels using ()
open import Cubical.Foundations.Isomorphism as Isomorphism using (Iso ; _Iso⟨_⟩_) renaming (_∎Iso to _Iso∎) public
open import Cubical.Foundations.Transport as Transport using ()
open import Cubical.Foundations.GroupoidLaws

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

  flipIso : ∀ {C : A → B → Type ℓ} → Iso ((a : A) (b : B) → C a b) ((b : B) (a : A) → C a b)
  flipIso .Iso.fun = flip
  flipIso .Iso.inv = flip
  flipIso .Iso.rightInv _ = refl
  flipIso .Iso.leftInv _ = refl

  flipEquiv : ∀ {C : A → B → Type ℓ} → ((a : A) (b : B) → C a b) ≃ ((b : B) (a : A) → C a b)
  flipEquiv {C} = strictIsoToEquiv (flipIso {C = C})

module _ where
  infixr 0 _≃⟨⟩_
  _≃⟨⟩_ : ∀ {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'} → A ≃ B → A ≃ B
  A ≃⟨⟩ e = e

  infixr 0 _Iso⟨⟩_
  _Iso⟨⟩_ : ∀ {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'} → Iso A B → Iso A B
  A Iso⟨⟩ i = i

module LevelNumber where
  open import Agda.Primitive using (LevelUniv)
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

  LevelTele : (n : Nat) → LevelUniv
  LevelTele zero = Level
  LevelTele (suc n) = Level → LevelTele n

  ℓMax : {n : Nat} → LevelTele n
  ℓMax {n = 0} = ℓ-zero
  ℓMax {n = 1} = λ ℓ → ℓ
  ℓMax {n = suc (suc n)} ℓ₀ ℓ₁ = ℓMax {n = suc n} (ℓ-max ℓ₀ ℓ₁)

ℓ-of : ∀ {ℓ} {A : Type ℓ} (a : A) → Level
ℓ-of {ℓ} _ = ℓ

open LevelNumber public

∂ : (i : I) → I
∂ i = i ∨ ~ i

∂² : (i j : I) → I
∂² i j = ∂ i ∨ ∂ j

module _ where
  private
    variable
      ℓ : Level
      A : Type ℓ
      x y z w v : A

  assoc-brace : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ v)
    → p ∙ ((q ∙ r) ∙ s) ≡ (p ∙ q) ∙ (r ∙ s)
  assoc-brace p q r s =
    p ∙ ((q ∙ r) ∙ s) ≡⟨ sym $ cong (p ∙_) (assoc q r s) ⟩
    p ∙ (q ∙ (r ∙ s)) ≡⟨ assoc p q (r ∙ s) ⟩
    (p ∙ q) ∙ (r ∙ s) ∎

  reflSquare : (x : A) → Square (refl′ x) (refl′ x) (refl′ x) (refl′ x)
  reflSquare x = λ i j → x

  compSquareFiller : (p : x ≡ y) (q : y ≡ z) (p∙q : x ≡ z) → Type _
  compSquareFiller {x} p q p∙q = Square p p∙q refl q

  pathComp→compSquareFiller : (p : x ≡ y) (q : y ≡ z) → compSquareFiller p q (p ∙ q)
  pathComp→compSquareFiller = compPath-filler

  PathCompFiller : (p : x ≡ y) (q : y ≡ z) → Type _
  PathCompFiller {x} {z} p q = Σ[ r ∈ x ≡ z ] compSquareFiller p q r

  pathComp→PathCompFiller : {p : x ≡ y} {q : y ≡ z} → PathCompFiller p q
  pathComp→PathCompFiller .fst = _
  pathComp→PathCompFiller .snd = pathComp→compSquareFiller _ _

  congPathCompFiller : ∀ {B : Type ℓ} (f : A → B) {p : x ≡ y} {q : y ≡ z} → PathCompFiller p q → PathCompFiller (cong f p) (cong f q)
  congPathCompFiller f (r , is-filler) .fst = cong f r
  congPathCompFiller f (r , is-filler) .snd = λ i j → f (is-filler i j)

  isPropCompSquareFiller : ∀ (p : x ≡ y) (q : y ≡ z) → isProp (PathCompFiller p q)
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

  module _ {A : Type ℓ} {x y z w : A} {p : x ≡ y} {q : y ≡ z} {r : x ≡ w} {s : w ≡ z} (sq : Square p s r q) where
    SquareDiag : x ≡ z
    SquareDiag i = sq i i

    diagFiller : compSquareFiller p q SquareDiag
    diagFiller i j = sq (j ∧ i) j

    diagFiller' : compSquareFiller r s SquareDiag
    diagFiller' i j = sq j (j ∧ i)

    SquareDiag≡pathComp : SquareDiag ≡ p ∙ q
    SquareDiag≡pathComp = sym $ compSquareFillerUnique diagFiller

    SquareDiag≡pathComp' : SquareDiag ≡ r ∙ s
    SquareDiag≡pathComp' = sym $ compSquareFillerUnique diagFiller'

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

  module _
    {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ')
    {x y : A} (p : x ≡ y)
    {x' : B x} {y' : B y}
    (p' : PathP (λ i → B (p i)) x' y')
    where
    rCancelP' : PathP (λ j → PathP (λ i → B (rCancel p j i)) x' x') (compPathP' {B = B} {p = p} {q = sym p} p' (symP p')) (refl′ x')
    rCancelP' j i =
      comp (λ k → B (rCancel-filler p k j i))
        (λ k → λ where
          (i = i0) → x'
          (i = i1) → p' (~ k ∧ ~ j)
          (j = i1) → x'
        )
        (p' (i ∧ ~ j))

  module _
    {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ')
    {x y : A} (p : x ≡ y)
    {x' : B x} {y' : B y}
    (p' : PathP (λ i → B (p i)) x' y')
    where
    lCancelP' : PathP (λ j → PathP (λ i → B (lCancel p j i)) y' y') (compPathP' {B = B} {p = sym p} {q = p} (symP p') p') (refl′ y')
    lCancelP' = rCancelP' B (sym p) (symP p')

  module _
    {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ')
    {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
    {x' : B x} {y' : B y} {z' : B z} {w' : B w}
    (p' : PathP (λ i → B (p i)) x' y')
    (q' : PathP (λ i → B (q i)) y' z')
    (r' : PathP (λ i → B (r i)) z' w')
    where
    doubleCompPathP'-base : (i j : I) → Type ℓ'
    doubleCompPathP'-base i j = B (doubleCompPath-filler p q r j i)

    doubleCompPathP'-faces : (i j : I) → Partial (∂ i) (B (doubleCompPath-filler p q r j i))
    doubleCompPathP'-faces i j (i = i0) = p' (~ j)
    doubleCompPathP'-faces i j (i = i1) = r' j

    doubleCompPathP' : PathP (λ i → B ((p ∙∙ q ∙∙ r) i)) x' w'
    doubleCompPathP' i = comp
      (doubleCompPathP'-base i)
      (doubleCompPathP'-faces i)
      (q' i)

    doubleCompPathP'-filler : PathP (λ j → PathP (λ i → (B (doubleCompPath-filler p q r j i))) (p' (~ j)) (r' j)) q' doubleCompPathP'
    doubleCompPathP'-filler j i = fill
      (doubleCompPathP'-base i)
      (doubleCompPathP'-faces i)
      (inS (q' i))
      j

  opaque
    compPath≡Square : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
      → (p ∙ s ≡ r ∙ q) ≡ (Square r s p q)
    compPath≡Square {A} {a} {d} {p} {q} {r} {s} = goal where
      open import Cubical.Foundations.Path
      open import Cubical.Foundations.Univalence

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

  doubleCompPath-cancel : {x y z w : A} (p : x ≡ y) (q : z ≡ w) (r : y ≡ w) → sym p ∙∙ (p ∙∙ r ∙∙ sym q) ∙∙ q ≡ r
  doubleCompPath-cancel {A} {x} {y} {z} {w} p q r = λ i j → hcomp {φ = ∂² i j} (sides i j) (base i j) where

    r′ : x ≡ z
    r′ = p ∙∙ r ∙∙ sym q

    r″ : y ≡ w
    r″ = sym p ∙∙ r′ ∙∙ q

    base : PathP (λ i → p i ≡ q i) r′ r
    base i j = doubleCompPath-filler p r (sym q) (~ i) j

    left : PathP (λ j → r′ j ≡ r″ j) p q
    left j k = doubleCompPath-filler (sym p) r′ q k j

    right : PathP (λ j → r j ≡ r j) (refl′ y) (refl′ w)
    right j k = r j

    sides : (i j k : I) → Partial (∂² i j) A
    sides i j k (i = i0) = left j k
    sides i j k (i = i1) = right j k
    sides i j k (j = i0) = p (i ∨ k)
    sides i j k (j = i1) = q (i ∨ k)

  module _ {x y z w : A} (p : x ≡ y) (q : z ≡ w) where
    doubleCompPathIso : Iso (x ≡ z) (y ≡ w)
    doubleCompPathIso .Iso.fun = sym p ∙∙_∙∙ q
    doubleCompPathIso .Iso.inv = p ∙∙_∙∙ sym q
    doubleCompPathIso .Iso.rightInv = doubleCompPath-cancel p q
    doubleCompPathIso .Iso.leftInv = doubleCompPath-cancel (sym p) (sym q)

    doubleCompPathEquiv : (x ≡ z) ≃ (y ≡ w)
    doubleCompPathEquiv .fst = sym p ∙∙_∙∙ q
    doubleCompPathEquiv .snd = Isomorphism.isoToIsEquiv doubleCompPathIso

module _ {ℓA ℓB ℓC} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
  (_□_ : A → B → C)
  where
    private
      cong-□ : ∀ {x y u v} → x ≡ y → u ≡ v → x □ u ≡ y □ v
      cong-□ p q = cong₂ _□_ p q

    module _
      {x₁ y₁ z₁ w₁ : A}
      {x₂ y₂ z₂ w₂ : B}
      (p₁ : x₁ ≡ y₁) (q₁ : y₁ ≡ z₁) (r₁ : z₁ ≡ w₁)
      (p₂ : x₂ ≡ y₂) (q₂ : y₂ ≡ z₂) (r₂ : z₂ ≡ w₂)
      where
        cong₂-∙∙-filler : (k j i : I) → C
        cong₂-∙∙-filler k j i = hfill sides base k where
          φ = i ∨ ~ i ∨ j ∨ ~ j

          sides : (k : I) → Partial φ C
          sides k (i = i0) = p₁ (~ k) □ p₂ (~ k)
          sides k (i = i1) = r₁ k □ r₂ k
          sides k (j = i0) = doubleCompPath-filler p₁ q₁ r₁ k i □ doubleCompPath-filler p₂ q₂ r₂ k i
          sides k (j = i1) = doubleCompPath-filler (cong-□ p₁ p₂) (cong-□ q₁ q₂) (cong-□ r₁ r₂) k i

          base : C [ φ ↦ sides i0 ]
          base = inS (q₁ i □ q₂ i)

        cong₂-∙∙ : cong₂ _□_ (p₁ ∙∙ q₁ ∙∙ r₁) (p₂ ∙∙ q₂ ∙∙ r₂) ≡ cong₂ _□_ p₁ p₂ ∙∙ cong₂ _□_ q₁ q₂ ∙∙ cong₂ _□_ r₁ r₂
        cong₂-∙∙ j i = cong₂-∙∙-filler i1 j i

    cong₂-∙ : {x₁ y₁ z₁ : A} {x₂ y₂ z₂ : B}
      (p₁ : x₁ ≡ y₁) (q₁ : y₁ ≡ z₁)
      (p₂ : x₂ ≡ y₂) (q₂ : y₂ ≡ z₂)
      → cong₂ _□_ (p₁ ∙ q₁) (p₂ ∙ q₂) ≡ cong₂ _□_ p₁ p₂ ∙ cong₂ _□_ q₁ q₂
    cong₂-∙ p₁ q₁ p₂ q₂ = cong₂-∙∙ refl p₁ q₁ refl p₂ q₂

module _
  {ℓA ℓB} {A : Type ℓA} {B : A → (i j : I) → Type ℓB}
  {f₀₀ : ∀ a → B a i0 i0}
  {f₀₁ : ∀ a → B a i0 i1}
  {f₀₋ : PathP (λ j → ∀ a → B a i0 j) f₀₀ f₀₁}
  {f₁₀ : ∀ a → B a i1 i0}
  {f₁₁ : ∀ a → B a i1 i1}
  {f₁₋ : PathP (λ j → ∀ a → B a i1 j) f₁₀ f₁₁}
  {f₋₀ : PathP (λ i → ∀ a → B a i i0) f₀₀ f₁₀}
  {f₋₁ : PathP (λ i → ∀ a → B a i i1) f₀₁ f₁₁} where

  funExtSquare :
      (f : (a : A) → SquareP (B a) (λ j → f₀₋ j a) (λ j → f₁₋ j a) (λ i → f₋₀ i a) (λ i → f₋₁ i a))
    → SquareP (λ i j → (a : A) → B a i j) f₀₋ f₁₋ f₋₀ f₋₁
  funExtSquare f i j a = f a i j

  funExtSquare⁻ :
      (sq : SquareP (λ i j → (a : A) → B a i j) f₀₋ f₁₋ f₋₀ f₋₁)
    → ((a : A) → SquareP (B a) (λ j → f₀₋ j a) (λ j → f₁₋ j a) (λ i → f₋₀ i a) (λ i → f₋₁ i a))
  funExtSquare⁻ sq a i j = sq i j a

  funExtSquareEquiv :
    ((a : A) → SquareP (B a) (λ j → f₀₋ j a) (λ j → f₁₋ j a) (λ i → f₋₀ i a) (λ i → f₋₁ i a))
      ≃
    (SquareP (λ i j → (a : A) → B a i j) f₀₋ f₁₋ f₋₀ f₋₁)
  unquoteDef funExtSquareEquiv = defStrictEquiv funExtSquareEquiv funExtSquare funExtSquare⁻

isGroupoid→isPropSquare : ∀ {ℓA} {A : Type ℓA} (_ : isGroupoid A)
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  → isProp (Square a₀₋ a₁₋ a₋₀ a₋₁)
isGroupoid→isPropSquare gpd-A sq₁ sq₂ = HLevels.isGroupoid→isGroupoid' gpd-A sq₁ sq₂ refl refl refl refl

isProp∃ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → isProp (∃[ a ∈ A ] B a)
isProp∃ A B = PT.isPropPropTrunc {A = Σ A B}

module _ where
  private
    variable
      ℓ ℓᴰ : Level
      A A′ A″ : Type ℓ
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
