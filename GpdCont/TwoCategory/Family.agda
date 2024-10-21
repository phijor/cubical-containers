module GpdCont.TwoCategory.Family where

open import GpdCont.Prelude renaming (J to AxiomJ)
open import GpdCont.TwoCategory.Base
open import GpdCont.HomotopySet

open import Cubical.Foundations.HLevels

module _ {ℓo ℓh ℓr} (C : TwoCategory ℓo ℓh ℓr) (ℓ : Level) where

  private
    module C = TwoCategory C

    -- rel : {x y : Σ[ J ∈ hSet ℓ ] (⟨ J ⟩ → C.ob)}
    --   → (f g : Σ[ φ ∈ (⟨ x .fst ⟩ → ⟨ y .fst ⟩) ] ∀ j → C.hom (x .snd j) (y .snd (φ j)))
    --   → Type _
    -- rel {x = (J , x)} {y = (K , y)} (φ , f) (ψ , g) =
    --   Σ[ ρ ∈ (⟨ J ⟩ → ⟨ K ⟩) ]
    --     Σ[ p₀ ∈ φ ≡ ρ ]
    --     Σ[ p₁ ∈ ψ ≡ ρ ]
    --       ∀ j {f′ g′ : C.hom (x j) (y (ρ j))}
    --         → PathP (λ i → C.hom (x j) (y (p₀ i j))) (f j) f′
    --         → PathP (λ i → C.hom (x j) (y (p₁ i j))) (g j) g′
    --         → C.rel {x = x j} {y = y (ρ j)} f′ g′

    rel : {x y : Σ[ J ∈ hSet ℓ ] (⟨ J ⟩ → C.ob)}
      → (f g : Σ[ φ ∈ (⟨ x .fst ⟩ → ⟨ y .fst ⟩) ] ∀ j → C.hom (x .snd j) (y .snd (φ j)))
      → Type _
    rel {x = (J , x)} {y = (K , y)} (φ , f) (ψ , g) =
      Σ[ p ∈ φ ≡ ψ ]
        ∀ j {g′ : C.hom (x j) (y (φ j))}
          → PathP (λ i → C.hom (x j) (y (p i j))) g′ (g j)
          → C.rel {x = x j} {y = y (φ j)} (f j) g′

    relJ : {x y : Σ[ J ∈ hSet ℓ ] (⟨ J ⟩ → C.ob)}
      → (f g : Σ[ φ ∈ (⟨ x .fst ⟩ → ⟨ y .fst ⟩) ] ∀ j → C.hom (x .snd j) (y .snd (φ j)))
      → Type ?
    relJ {x = (J , x)} {y = (K , y)} (φ , f) (ψ , g) =
      (j : ⟨ J ⟩) → (p : φ j ≡ ψ j) → AxiomJ (λ k (p : φ j ≡ k) → {! !}) {! !} p

    {-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}
          -- → C.rel (f j) (subst (λ · → C.hom (x j) (y (· j))) (sym p) (g j))

  Fam : TwoCategory (ℓ-max ℓo (ℓ-suc ℓ)) (ℓ-max ℓh ℓ) (ℓ-max (ℓ-max ℓh ℓr) ℓ)
  Fam .TwoCategory.ob = Σ[ J ∈ hSet ℓ ] ((j : ⟨ J ⟩) → C.ob)
  Fam .TwoCategory.hom (J , x) (K , y) = Σ[ φ ∈ (⟨ J ⟩ → ⟨ K ⟩) ] ∀ j → C.hom (x j) (y $ φ j)
  Fam .TwoCategory.rel {x} {y} = rel {x} {y}
  Fam .TwoCategory.two-category-structure = fam-str where
    fam-str : TwoCategoryStr _ _ _
    fam-str .TwoCategoryStr.id-hom (J , x) = id ⟨ J ⟩ , C.id-hom ∘ x
    fam-str .TwoCategoryStr.comp-hom (φ , f) (ψ , g) = φ ⋆ ψ , λ j → f j C.∙₁ g (φ j)
    fam-str .TwoCategoryStr.id-rel (φ , f) = refl , λ j p → subst (C.rel (f j)) (sym p) (C.id-rel (f j))
    fam-str .TwoCategoryStr.trans (p , r) (q , s) .fst = p ∙ q
    fam-str .TwoCategoryStr.trans (p , r) (q , s) .snd = λ j {g′} P → C.trans {!r j !} {! !}
    fam-str .TwoCategoryStr.comp-rel = {! !}
  Fam .TwoCategory.is-two-category = {! !}
