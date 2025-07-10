module GpdCont.Group.SemidirectProduct where

open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms

open import GpdCont.Prelude
open import GpdCont.HomotopySet
open import GpdCont.GroupAction.Base

private
  Group→hSet : ∀ {ℓ} → (H : Group ℓ) → hSet ℓ
  Group→hSet H .fst = ⟨ H ⟩
  Group→hSet H .snd = str H .GroupStr.is-set

module _ {ℓN ℓH} (N : Group ℓN) (H : Group ℓH) (φ : Action H (Group→hSet N)) where

  private
    G = ⟨ N ⟩ × ⟨ H ⟩

    module N = GroupStr (str N)
    module H = GroupStr (str H)
    module φ = Action φ

    _·_ : G → G → G
    ((n₁ , h₁) · (n₂ , h₂)) .fst = n₁ N.· (h₁ φ.▷ n₂)
    ((n₁ , h₁) · (n₂ , h₂)) .snd = h₁ H.· h₂

    1g : G
    1g .fst = N.1g
    1g .snd = H.1g

    id-right : (g : G) → g · 1g ≡ g
    id-right (n , h) = ≡-× p₁ {! !} where
      p₁ : n N.· (h φ.▷ N.1g) ≡ n
      p₁ = {! !}

    inv : G → G
    inv (n , h) .fst = invEq (φ.action (H.inv h)) (N.inv n)
    inv (n , h) .snd = H.inv h

  SemidirProd : Group (ℓ-max ℓN ℓH)
  SemidirProd .fst = G
  SemidirProd .snd .GroupStr.1g = 1g
  SemidirProd .snd .GroupStr._·_ = _·_
  SemidirProd .snd .GroupStr.inv = inv
  SemidirProd .snd .GroupStr.isGroup = makeIsGroup {! !}
    {! !}
    id-right
    {! !}
    {! !}
    {! !}

⋊-syntax : ∀ {ℓN ℓH} (N : Group ℓN) (H : Group ℓH) → Action H (Group→hSet N) → Group (ℓ-max ℓN ℓH)
⋊-syntax = SemidirProd

infix 10 ⋊-syntax
syntax ⋊-syntax N H φ = N ⋊[ φ ] H

module _
  {ℓN₀ ℓN₁ ℓH₀ ℓH₁}
  {N₀ : Group ℓN₀} {N₁ : Group ℓN₁}
  {H₀ : Group ℓH₀} {H₁ : Group ℓH₁}
  (φ₀ : Action H₀ (Group→hSet N₀))
  (φ₁ : Action H₁ (Group→hSet N₁))
  (ν* : GroupEquiv N₀ N₁)
  (η* : GroupEquiv H₀ H₁)
  where
  private
    ν = equivFun (ν* .fst)
    η = equivFun (η* .fst)
    module ν = IsGroupHom (ν* .snd)
    module η = IsGroupHom (η* .snd)
    module N₀ = GroupStr (str N₀)
    module N₁ = GroupStr (str N₁)
    module H₀ = GroupStr (str H₀)
    module H₁ = GroupStr (str H₁)
    module φ₀ = Action φ₀
    module φ₁ = Action φ₁

  SemidirectProductEquiv :
    (p : ∀ n h → ν (h φ₀.▷ n) ≡ η h φ₁.▷ ν n)
    → GroupEquiv (N₀ ⋊[ φ₀ ] H₀) (N₁ ⋊[ φ₁ ] H₁)
  SemidirectProductEquiv p = goal where
    equiv : ⟨ N₀ ⟩ × ⟨ H₀ ⟩ ≃ ⟨ N₁ ⟩ × ⟨ H₁ ⟩
    equiv = Σ-cong-equiv (ν* .fst) λ _ → η* .fst

    opaque
      is-hom-equiv : IsGroupHom (str $ SemidirProd N₀ H₀ φ₀) (equivFun equiv) (str $ SemidirProd N₁ H₁ φ₁)
      is-hom-equiv .IsGroupHom.pres· (n , h) (n' , h') = ΣPathP (lem₁ , lem₂) where
        lem₁ : ν (n N₀.· (h φ₀.▷ n')) ≡ ν n N₁.· (η h φ₁.▷ ν n')
        lem₁ = ν.pres· _ _ ∙ cong (ν n N₁.·_) (p n' h)

        lem₂ : η (h H₀.· h') ≡ (η h) H₁.· (η h')
        lem₂ = η.pres· h h'
      is-hom-equiv .IsGroupHom.pres1 = ΣPathP (ν.pres1 , η.pres1)
      is-hom-equiv .IsGroupHom.presinv (n , h) = ΣPathP (lem₁ , η.presinv h) where
        lem₁ : ν ((H₀.inv h) φ₀.▷⁻ (N₀.inv n)) ≡ (H₁.inv (η h) φ₁.▷⁻ N₁.inv (ν n))
        lem₁ =
          ν ((H₀.inv h) φ₀.▷⁻ (N₀.inv n)) ≡⟨ cong ν (ActionProperties.action-inv-inv φ₀ h ≡$ N₀.inv n) ⟩
          ν (h φ₀.▷ (N₀.inv n)) ≡⟨ p (N₀.inv n) h ⟩
          (η h φ₁.▷ ν (N₀.inv n)) ≡⟨ sym (ActionProperties.action-inv-inv φ₁ (η h) ≡$ _) ⟩
          (H₁.inv (η h) φ₁.▷⁻ ν (N₀.inv n)) ≡[ i ]⟨ (H₁.inv (η h) φ₁.▷⁻ ν.presinv n i) ⟩
          (H₁.inv (η h) φ₁.▷⁻ N₁.inv (ν n)) ∎

    goal : GroupEquiv _ _
    goal .fst = equiv
    goal .snd = is-hom-equiv
