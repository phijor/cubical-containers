module GpdCont.Delooping where

open import GpdCont.Prelude

open import Cubical.Foundations.HLevels

module Delooping {ℓ} (G : Type ℓ) (_·_ : G → G → G) where
  data 𝔹 : Type ℓ where
    ⋆ : 𝔹
    loop : (g : G) → ⋆ ≡ ⋆
    loop-comp : (g h : G)
      → Square (loop g) (loop (g · h)) refl (loop h)
      -- ⋆ ---[ g ]--- ⋆
      -- | · →         |
      -- | ↓         [ h ]
      -- |             |
      -- ⋆ -[ g · h ]- ⋆
    isGroupoid𝔹 : isGroupoid 𝔹

  elim : ∀ {B : 𝔹 → Type ℓ}
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
  elim is-gpd-B b b-loop b-comp = go where
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

  rec : ∀ {B : Type ℓ}
    → isGroupoid B
    → (b : B)
    → (b-loop : (g : G) → b ≡ b)
    → (b-comp : (g h : G) → Square (b-loop g) (b-loop (g · h)) refl (b-loop h))
    → 𝔹 → B
  rec {B} is-gpd-B b b-loop b-comp = go where
    go : 𝔹 → B
    go ⋆ = b
    go (loop g i) = b-loop g i
    go (loop-comp g h i j) = b-comp g h i j
    go (isGroupoid𝔹 x y p q r s i j k) = is-gpd-B (go x) (go y) (cong go p) (cong go q) (cong (cong go) r) (cong (cong go) s) i j k
