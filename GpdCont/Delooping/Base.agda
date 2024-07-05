open import GpdCont.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base

module GpdCont.Delooping.Base {ℓ} (G : Type ℓ) (γ : GroupStr G) where
  private
    open module G = GroupStr γ using (_·_)

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

  recSet : ∀ {ℓB} {B : Type ℓB}
    → isSet B
    → (b : B)
    → (b-loop : (g : G) → b ≡ b)
    → 𝔹 → B
  recSet {B} is-set-B b b-loop = rec {B = B} (isSet→isGroupoid is-set-B) b b-loop b-comp where
    opaque
      b-comp : (g h : G) → compSquareFiller (b-loop g) (b-loop h) (b-loop (g · h))
      b-comp g h = isSet→SquareP (λ i j → is-set-B) (b-loop g) (b-loop (g · h)) refl (b-loop h)
