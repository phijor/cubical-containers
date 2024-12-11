module GpdCont.GroupAction.Pi where

open import GpdCont.Prelude
open import GpdCont.GroupAction.Base
open import GpdCont.Equiv using (equivΠCodComp)
open import GpdCont.HomotopySet using (ΠSet ; ΣSet ; _→Set_)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (preCompEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (flip)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)

private
  variable
    ℓ : Level
    G : Group ℓ
    X : hSet ℓ

open Action using (action ; pres·)

ΠActionΣ : ∀ {ℓG ℓS} (S : hSet ℓS)
  → (X : ⟨ S ⟩ → hSet ℓ)
  → {G : ⟨ S ⟩ → Group ℓG}
  → (∀ s → Action (G s) (X s))
  → Action (ΠGroup G) (ΣSet S X)
ΠActionΣ S X {G} σ = act where
  open module G {s : ⟨ S ⟩} = GroupStr (str (G s)) using (_·_)

  ΠG = ∀ s → ⟨ G s ⟩
  ΣX = Σ[ s ∈ ⟨ S ⟩ ] ⟨ X s ⟩

  Σσ : (g : ΠG) → ΣX ≃ ΣX
  Σσ g = Σ-cong-equiv-snd λ s → σ s .action (g s)

  Σσ-pres·-ext : ∀ (g h : ΠG) (s : ⟨ S ⟩) → (σ s ⁺ (g s · h s)) ≡ (σ s ⁺ h s) ∘ (σ s ⁺ g s)
  Σσ-pres·-ext g h s = cong equivFun (σ s .pres· (g s) (h s))

  Σσ-pres· : ∀ g h → Σσ (λ s → g s · h s) ≡ Σσ g ∙ₑ Σσ h
  Σσ-pres· g h = equivEq λ { i (s , x) → s , Σσ-pres·-ext g h s i x }

  act : Action _ _
  act .action = Σσ
  act .pres· = Σσ-pres·

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

-- Any G-action on X also acts on functions (f : X → Y) by precomposition.
-- Note that in order the respect variance (σ acts on X, which is in a negative
-- position), the action inverts group elements:
--
--    σ*(g) : (X → Y) → (X → Y)
--    σ*(g) = λ f → f ∘ σ(g⁻¹)
preCompAction : ∀ {ℓG ℓX ℓY} {G : Group ℓG} {X : hSet ℓX}
  → (σ : Action G X)
  → (Y : hSet ℓY)
  → Action G (X →Set Y)
preCompAction {G} σ Y = σ* where
  open module G = GroupStr (str G) using (_·_ ; inv)

  σ*-pres· : ∀ g h → (σ ⁺ inv (g · h)) ≡ ((σ ⁺ inv g) ∘ (σ ⁺ inv h))
  σ*-pres· g h =
    (σ ⁺ inv (g · h)) ≡⟨ ActionProperties.action-inv σ _ ⟩
    invEq (action σ (g · h)) ≡⟨ cong invEq (σ .pres· g h) ⟩
    invEq (action σ g ∙ₑ action σ h) ≡⟨⟩
    (invEq (action σ g) ∘ invEq (action σ h)) ≡[ i ]⟨ (ActionProperties.action-inv σ g (~ i)) ∘ (ActionProperties.action-inv σ h (~ i)) ⟩
    ((σ ⁺ inv g) ∘ (σ ⁺ inv h)) ∎

  σ* : Action _ _
  σ* .action g = preCompEquiv $ σ .action $ inv g
  σ* .pres· g h = equivEq $ funExt λ f → cong (f ∘_) $ σ*-pres· g h
