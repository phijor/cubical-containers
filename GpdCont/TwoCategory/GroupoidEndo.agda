module GpdCont.TwoCategory.GroupoidEndo where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Isomorphism
open import GpdCont.TwoCategory.TwoDiscrete using (TwoDiscrete)
open import GpdCont.WildCat.TypeOfHLevel using (hGroupoidEndo ; isGroupoidEndoNatTrans)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

private
  variable
    ℓ ℓ' : Level
    X Y Z : Type ℓ

  isGroupoid→ : isGroupoid Y → isGroupoid (X → Y)
  isGroupoid→ = isGroupoidΠ ∘ const

  _→Gpd_ : (X Y : hGroupoid ℓ) → hGroupoid ℓ
  X →Gpd Y = (⟨ X ⟩ → ⟨ Y ⟩) , isGroupoid→ (str Y)

  _∙htpy_ : ∀ {f₁ f₂ : X → Y} {g₁ g₂ : Y → Z}
    → (p : f₁ ≡ f₂)
    → (q : g₁ ≡ g₂)
    → (f₁ ⋆ g₁ ≡ f₂ ⋆ g₂)
  _∙htpy_ p q = cong₂ _⋆_ p q
  
module _ (ℓ : Level) where
  Endo : TwoCategory (ℓ-suc ℓ) (ℓ-suc ℓ) (ℓ-suc ℓ)
  Endo = TwoDiscrete (hGroupoidEndo ℓ) (isGroupoidEndoNatTrans ℓ)
