module GpdCont.GroupAction.Pi where

open import GpdCont.Prelude
open import GpdCont.GroupAction.Base
open import GpdCont.Equiv using (equivΠCodComp)
open import GpdCont.HomotopySet using (ΠSet)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base

open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)

private
  variable
    ℓ : Level
    G : Group ℓ
    X : hSet ℓ

open Action using (action ; pres·)

ΠAction : ∀ {ℓG ℓS} {S : Type ℓS} {G : S → Group ℓG}
  → (X : S → hSet ℓ)
  → (∀ s → Action (G s) (X s))
  → Action (ΠGroup G) (ΠSet X)
ΠAction {S} {G} X σ = act where
  open module G {s : S} = GroupStr (str (G s)) using (_·_)

  σ* : (g : ∀ s → ⟨ G s ⟩) → (∀ s → ⟨ X s ⟩) ≃ (∀ s → ⟨ X s ⟩)
  σ* g = equivΠCod λ s → σ s .action (g s)

  σ-pres· : ∀ g h → σ* (λ s → g s · h s) ≡ σ* g ∙ₑ σ* h
  σ-pres· g h =
    σ* (λ s → g s · h s) ≡⟨ cong equivΠCod $ funExt (λ s → σ s .pres· (g s) (h s)) ⟩
    equivΠCod (λ s → σ s .action (g s) ∙ₑ σ s .action (h s)) ≡⟨ equivΠCodComp _ _ ⟩
    σ* g ∙ₑ equivΠCod (λ s → σ s .action (h s)) ∎

  act : Action _ _
  act .action = σ*
  act .pres· = σ-pres·
