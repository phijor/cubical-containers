module GpdCont.SymmetricContainer.Substitute where

open import GpdCont.Prelude hiding (_◁_)
open import GpdCont.HomotopySet
open import GpdCont.Polynomial
open import GpdCont.SymmetricContainer.Base
open import GpdCont.SymmetricContainer.Eval

open import GpdCont.ActionContainer.Base
open import GpdCont.ActionContainer.Delooping

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

module Subst (F G : SymmetricContainer ℓ) where
  private
    module F = SymmetricContainer F
    module G = SymmetricContainer G

  subst-shape : hGroupoid ℓ
  subst-shape = ⟦ F ⟧ G.ShapeGroupoid

  subst-pos : ⟨ subst-shape ⟩ → hSet ℓ
  subst-pos poly⟨ s , l ⟩ = ΣSet (F.PosSet s) λ p → G.PosSet (l p)

  def : SymmetricContainer ℓ
  def = [ s ∈ subst-shape ◁ subst-pos s ]

_⟪_⟫ : (F G : SymmetricContainer ℓ) → SymmetricContainer ℓ
_⟪_⟫ = Subst.def

module Test (F G : ActionContainer ℓ) where
  open Container using () renaming (Delooping to 𝔹)
  open SymmetricContainer using (Shape)

  private
    module 𝔹-Notation (F : ActionContainer ℓ) where
      open Container F using (⋆ ; Delooping ; DeloopingShape ; 𝔹Symm) public
      open SymmetricContainer Delooping public

    module F = ActionContainer F
    module 𝔹F = 𝔹-Notation F

    module G = ActionContainer G
    module 𝔹G = 𝔹-Notation G

  test-shape : ((𝔹 F) ⟪ (𝔹 G) ⟫) .Shape ≃ (Σ[ s ∈ F.Shape ] {! !})
  test-shape =
    ((𝔹 F) ⟪ (𝔹 G) ⟫) .Shape ≃⟨⟩
    ⟨ ⟦ 𝔹 F ⟧ 𝔹G.ShapeGroupoid ⟩ ≃⟨ _ ≃Σ ⟩
    Σ[ s ∈ 𝔹F.Shape ] (𝔹F.Pos s → 𝔹G.Shape) ≃⟨⟩
    Σ[ s ∈ 𝔹F.Shape ] (𝔹F.Pos s → Σ G.Shape 𝔹G.𝔹Symm) ≃⟨ Σ-cong-equiv-snd (λ s → Σ-Π-≃) ⟩
    Σ[ s ∈ 𝔹F.Shape ] (Σ[ f ∈ (𝔹F.Pos s → G.Shape) ] ∀ y → 𝔹G.𝔹Symm (f y)) ≃⟨ Σ-assoc-≃ ⟩
    Σ[ s ∈ F.Shape ] (Σ[ x ∈ 𝔹F.𝔹Symm s ] Σ[ f ∈ (𝔹F.Pos (s , x) → G.Shape) ] ((y : 𝔹F.Pos (s , x)) → 𝔹G.𝔹Symm (f y))) ≃⟨ {! !} ⟩
    {! !} ≃∎
    where
      H : (s : F.Shape) → hGroupoid ℓ
      H s .fst = Σ[ x ∈ 𝔹F.𝔹Symm s ] Σ[ f ∈ (𝔹F.Pos (s , x) → G.Shape) ] ((y : 𝔹F.Pos (s , x)) → 𝔹G.𝔹Symm (f y))
      H s .snd = {! !}

      H⋆ : ∀ s → ⟨ H s ⟩
      H⋆ s .fst = 𝔹F.⋆
      H⋆ s .snd .fst = the (F.Pos s → G.Shape) {! !}
      H⋆ s .snd .snd = {! !}
