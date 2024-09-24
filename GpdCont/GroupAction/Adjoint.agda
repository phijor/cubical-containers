open import GpdCont.Prelude
open import GpdCont.HomotopySet using (_→Set_)
open import GpdCont.GroupAction.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base

module GpdCont.GroupAction.Adjoint
  {ℓ ℓG}
  (G : Group ℓG)
  (X Y : hSet ℓ)
  (σ : Action G X)
  (τ : Action G Y)
  where
  private
    open module G = GroupStr (str G) using (_·_)

  open Action using (action ; pres·)

  adj : ⟨ G ⟩ → (⟨ X ⟩ → ⟨ Y ⟩) ≃ (⟨ X ⟩ → ⟨ Y ⟩)
  adj g = equiv→ (σ .action g) (τ .action g)

  opaque
    adj-pres· : (g h : ⟨ G ⟩) → adj (g · h) ≡ adj g ∙ₑ adj h
    adj-pres· g g′ =
      adj (g · g′) ≡⟨ cong₂ equiv→ (σ .pres· g g′) (τ .pres· g g′) ⟩
      equiv→ (σ .action g ∙ₑ σ .action g′) (τ .action g ∙ₑ τ .action g′) ≡⟨ equivEq refl ⟩
      adj g ∙ₑ adj g′ ∎

  AdjointAction : Action G (X →Set Y)
  AdjointAction .action = adj
  AdjointAction .pres· = adj-pres·
