open import GpdCont.Prelude hiding (_⋆_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_∙ₑ_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Algebra.Group.Base

module GpdCont.Delooping.Base {ℓ} (G : Type ℓ) (γ : GroupStr G) where
  private
    open module G = GroupStr γ using (_·_ ; inv ; 1g)

  data 𝔹 : Type ℓ where
    ⋆ : 𝔹
    loop : (g : G) → ⋆ ≡ ⋆
    loop-comp : (g h : G) → compSquareFiller (loop g) (loop h) (loop (g · h))
      -- ⋆ ---[ g ]--- ⋆
      -- | · →         |
      -- | ↓         [ h ]
      -- |             |
      -- ⋆ -[ g · h ]- ⋆
    isGroupoid𝔹 : isGroupoid 𝔹

  loop-∙ : (g h : G) → loop g ∙ loop h ≡ loop (g · h)
  loop-∙ g h = compSquareFillerUnique (loop-comp g h)

  loop-comp-coerce : ∀ {g h k} → g · h ≡ k → compSquareFiller (loop g) (loop h) (loop k)
  loop-comp-coerce {g} {h} {k} p = coerceCompSquareFiller (loop-∙ g h ∙ cong loop p)

  loop-1 : loop 1g ≡ refl
  loop-1 i j = hcomp sides (base i j) where
    lhs : Square refl (sym $ loop 1g) (loop (1g · 1g)) (loop 1g)
    lhs j k = loop-comp 1g 1g (~ k) j

    rhs : Square refl (sym $ loop 1g) (loop 1g) refl
    rhs j k = loop 1g (j ∧ ~ k)

    sides : (k : I) → Partial (∂² i j) 𝔹
    sides k (i = i0) = lhs j k
    sides k (i = i1) = rhs j k
    sides k (j = i0) = ⋆
    sides k (j = i1) = loop 1g (~ k)

    base : loop (1g · 1g) ≡ loop 1g
    base = cong loop (G.·IdL 1g)

  loop-1-coerce : {g : G} → g ≡ 1g → loop g ≡ refl
  loop-1-coerce p = cong loop p ∙ loop-1

  loop-inv-left : (g : G) → loop (inv g · g) ≡ refl
  loop-inv-left g = loop-1-coerce (G.·InvL g)

  loop-inv-right : (g : G) → loop (g · inv g) ≡ refl
  loop-inv-right g = loop-1-coerce (G.·InvR g)

  loop-inv : (g : G) → loop (inv g) ≡ sym (loop g)
  loop-inv g i j = hcomp sides (base i j) where
    lhs : Square refl (sym $ loop g) (loop $ inv g · g) (loop $ inv g)
    lhs j k = loop-comp (inv g) g (~ k) j

    rhs : Square refl (sym $ loop g) refl (sym $ loop g)
    rhs j k = loop g (~ j ∨ ~ k)

    sides : (k : I) → Partial (∂ i ∨ ∂ j) 𝔹
    sides k (i = i0) = lhs j k
    sides k (i = i1) = rhs j k
    sides k (j = i0) = ⋆
    sides k (j = i1) = loop g (~ k)

    base : loop (inv g · g) ≡ refl
    base = loop-inv-left g

  elimDep : ∀ {ℓB} {B : 𝔹 → Type ℓB}
    → (isOfHLevelDep 3 B)
    → (b : B ⋆)
    → (b-loop : (g : G) → PathP (λ i → B (loop g i)) b b)
    → (b-comp : (g h : G)
      → SquareP (λ i j → B (loop-comp g h i j))
        (b-loop g)
        (b-loop (g · h))
        refl
        (b-loop h))
    → (x : 𝔹) → B x
  elimDep is-gpd-B b b-loop b-comp = go where
    go : ∀ x → _
    go ⋆ = b
    go (loop g i) = b-loop g i
    go (loop-comp g h i j) = b-comp g h i j
    go (isGroupoid𝔹 x y p q r s i j k) =
      is-gpd-B {x} {y}
        (go x) (go y)
        (cong go p) (cong go q)
        (cong (cong go) r) (cong (cong go) s)
        (isGroupoid𝔹 x y p q r s)
        i j k

  elim : ∀ {ℓB} {B : 𝔹 → Type ℓB}
    → (∀ x → isGroupoid (B x))
    → (b : B ⋆)
    → (b-loop : (g : G) → PathP (λ i → B (loop g i)) b b)
    → (b-comp : (g h : G)
      → SquareP (λ i j → B (loop-comp g h i j))
        (b-loop g)
        (b-loop (g · h))
        refl
        (b-loop h))
    → (x : 𝔹) → B x
  elim is-gpd-B = elimDep λ {a0} {a1} → isOfHLevel→isOfHLevelDep 3 is-gpd-B {a0} {a1}

  elimSetDep : ∀ {ℓB} {B : 𝔹 → Type ℓB}
    → (isOfHLevelDep 2 B)
    → (b : B ⋆)
    → (b-loop : (g : G) → PathP (λ i → B (loop g i)) b b)
    → (x : 𝔹) → B x
  elimSetDep {B} is-set-B b b-loop = elimDep is-gpd-B b b-loop b-loop-comp where
    is-gpd-B : isOfHLevelDep 3 B
    is-gpd-B b₀ b₁ = isPropDep→isSetDep (is-set-B b₀ b₁)

    opaque
      b-loop-comp : (g h : G)
        → SquareP
          (λ i j → B (loop-comp g h i j))
          (b-loop g)
          (b-loop (g · h)) (refl {x = b})
          (b-loop h)
      b-loop-comp g h = isSet→SquareP
        (λ i j x y p q → is-set-B x y p q λ _ _ → loop-comp g h i j)
        (b-loop g) (b-loop (g · h)) refl (b-loop h)

  elimSet : ∀ {ℓB} {B : 𝔹 → Type ℓB}
    → (∀ x → isSet (B x))
    → (b : B ⋆)
    → (b-loop : (g : G) → PathP (λ i → B (loop g i)) b b)
    → (x : 𝔹) → B x
  elimSet {B} is-set-B b b-loop = elimSetDep {B = B} (λ {a0} {a1} → isOfHLevel→isOfHLevelDep 2 is-set-B {a0} {a1}) b b-loop

  elimPropDep : ∀ {ℓB} {B : 𝔹 → Type ℓB} → (isPropDep B) → (b : B ⋆) → (x : 𝔹) → B x
  elimPropDep {B} is-prop-B b = elimSetDep is-set-B b b-loop where
    is-set-B : isOfHLevelDep 2 B
    is-set-B = isPropDep→isSetDep is-prop-B

    opaque
      b-loop : (g : G) → PathP (λ i → B (loop g i)) b b
      b-loop g = is-prop-B b b (loop g)

  elimProp : ∀ {ℓB} {B : 𝔹 → Type ℓB} → (∀ x → isProp (B x)) → (b : B ⋆) → (x : 𝔹) → B x
  elimProp {B} is-prop-B = elimPropDep λ {a0} {a1} → isOfHLevel→isOfHLevelDep 1 is-prop-B {a0} {a1}

  opaque
    elimProp2 : ∀ {ℓB} {B : (x y : 𝔹) → Type ℓB} → (∀ x y → isProp (B x y)) → (b : B ⋆ ⋆) → (x y : 𝔹) → B x y
    elimProp2 {B} is-prop-B b = elimProp (λ x → isPropΠ λ y → is-prop-B x y) (elimProp (is-prop-B _) b)

  rec : ∀ {ℓB} {B : Type ℓB}
    → isGroupoid B
    → (b : B)
    → (b-loop : (g : G) → b ≡ b)
    → (b-comp : (g h : G) → compSquareFiller (b-loop g) (b-loop h) (b-loop (g · h)))
    → 𝔹 → B
  rec {B} is-gpd-B b b-loop b-comp = go where
    go : 𝔹 → B
    go ⋆ = b
    go (loop g i) = b-loop g i
    go (loop-comp g h i j) = b-comp g h i j
    go (isGroupoid𝔹 x y p q r s i j k) = is-gpd-B (go x) (go y) (cong go p) (cong go q) (cong (cong go) r) (cong (cong go) s) i j k

  rec∙ : ∀ {ℓB} {B : Type ℓB}
    → isGroupoid B
    → (b : B)
    → (b-loop : (g : G) → b ≡ b)
    → (b-comp : (g h : G) → (b-loop g) ∙ (b-loop h) ≡ (b-loop (g · h)))
    → 𝔹 → B
  rec∙ is-gpd-B b b-loop b-comp-∙ = rec is-gpd-B b b-loop b-comp where
    b-comp = λ g h → coerceCompSquareFiller (b-comp-∙ g h)

  recSet : ∀ {ℓB} {B : Type ℓB}
    → isSet B
    → (b : B)
    → (b-loop : (g : G) → b ≡ b)
    → 𝔹 → B
  recSet {B} is-set-B b b-loop = rec {B = B} (isSet→isGroupoid is-set-B) b b-loop b-comp where
    opaque
      b-comp : (g h : G) → compSquareFiller (b-loop g) (b-loop h) (b-loop (g · h))
      b-comp g h = isSet→SquareP (λ i j → is-set-B) (b-loop g) (b-loop (g · h)) refl (b-loop h)

  rec→hSet : ∀ {ℓB}
    → (X⋆ : hSet ℓB)
    → (X-loop : (g : G) → ⟨ X⋆ ⟩ ≃ ⟨ X⋆ ⟩)
    → (X-comp : (g h : G) → X-loop (g · h) ≡ X-loop g ∙ₑ X-loop h)
    → 𝔹 → hSet ℓB
  rec→hSet X⋆ X-loop X-comp = rec isGroupoidHSet X⋆ X-loop′ X-comp′ where
    open import GpdCont.Univalence using (ua ; uaCompEquiv)
    open import GpdCont.HomotopySet using (hSet≡)

    X-loop′ : G → X⋆ ≡ X⋆
    X-loop′ = hSet≡ ∘ ua ∘ X-loop

    opaque
      X-comp′ : ∀ g h → compSquareFiller (X-loop′ g) (X-loop′ h) (X-loop′ (g · h))
      X-comp′ g h = ΣSquareSet (λ X → isProp→isSet isPropIsSet) $ coerceCompSquareFiller $
          (ua $ X-loop g) ∙ (ua $ X-loop h) ≡⟨ sym $ uaCompEquiv (X-loop g) (X-loop h) ⟩
          (ua $ X-loop g ∙ₑ X-loop h) ≡⟨ sym $ cong ua (X-comp g h) ⟩
          (ua $ X-loop (g · h)) ∎

  {-# INLINE elimDep #-}
  {-# INLINE elimSetDep #-}
  {-# INLINE elimPropDep #-}
  {-# INLINE elim #-}
  {-# INLINE elimSet #-}
  {-# INLINE elimProp #-}
  {-# INLINE rec #-}
  {-# INLINE recSet #-}
