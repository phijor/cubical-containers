module GpdCont.Group.WreathProduct where

open import GpdCont.Prelude
open import GpdCont.Equiv
open import GpdCont.HomotopySet
open import GpdCont.GroupAction.Base
open import GpdCont.Group.SemidirectProduct

open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)


module _ {ℓΩ ℓA ℓH} (Ω : hSet ℓΩ) (A : Group ℓA) (H : Group ℓH) (φ : Action H Ω) where
  private
    ΠA : Group _
    ΠA = ΠGroup {X = ⟨ Ω ⟩} (const A)

    ΠASet : hSet _
    ΠASet .fst = ⟨ ΠA ⟩
    ΠASet .snd = str ΠA .GroupStr.is-set

    module H = GroupStr (str H)
    module φ where
      open Action φ public
      open ActionProperties φ public


  WreathAction : Action H ΠASet
  WreathAction .Action.action h = equivΠDomain (invEquiv (φ.action h))
  WreathAction .Action.pres· h h′ = equivEq (funExt₂ goal) where
    φ⁻ : ⟨ H ⟩ → ⟨ Ω ⟩ → ⟨ Ω ⟩
    φ⁻ = invEq ∘ φ.action

    goal : (as : ⟨ Ω ⟩ → ⟨ A ⟩) (ω : ⟨ Ω ⟩) → as (φ⁻ (h H.· h′) ω) ≡ as (φ⁻ h (φ⁻ h′ ω))
    goal as ω = cong as $
      (φ⁻ (h H.· h′) ω) ≡⟨ φ.action-inv-comp h h′ ≡$ ω ⟩
      (φ⁻ h (φ⁻ h′ ω)) ∎

  Wreath : Group (ℓ-max (ℓ-max ℓΩ ℓA) ℓH)
  Wreath = ΠA ⋊[ WreathAction ] H

module _ {ℓ}
  {Ω₀ Ω₁ : hSet ℓ}
  (ω : ⟨ Ω₀ ⟩ ≃ ⟨ Ω₁ ⟩)
  {A₀ A₁ : Group ℓ}
  (α : GroupEquiv A₀ A₁)
  {H₀ H₁ : Group ℓ}
  {φ₀ : Action H₀ Ω₀}
  {φ₁ : Action H₁ Ω₁}
  (η : GroupEquiv H₀ H₁)
  where
  private
    module α = IsGroupHom (α .snd)
    module φ₀ = Action φ₀

    ΠA-equiv : GroupEquiv (ΠGroup {X = ⟨ Ω₀ ⟩} $ const A₀) (ΠGroup {X = ⟨ Ω₁ ⟩} $ const A₁)
    ΠA-equiv .fst = equiv→ ω (α .fst)
    ΠA-equiv .snd .IsGroupHom.pres· _ _ = funExt λ _ → α.pres· _ _
    ΠA-equiv .snd .IsGroupHom.pres1 = funExt λ _ → α.pres1
    ΠA-equiv .snd .IsGroupHom.presinv _ = funExt λ _ → α.presinv _

  WreathEquiv :
    (∀ h → (φ₀ ⁻ h) ∘ invEq ω ≡ (invEq ω) ∘ (φ₁ ⁻ equivFun (η .fst) h))
    → GroupEquiv (Wreath Ω₀ A₀ H₀ φ₀) (Wreath Ω₁ A₁ H₁ φ₁)
  WreathEquiv comm = SemidirectProductEquiv _ _ ΠA-equiv η equivariant where
    equivariant : (a : ⟨ Ω₀ ⟩ → ⟨ A₀ ⟩) (h : ⟨ H₀ ⟩)
      → equivFun (α .fst) ∘ a ∘ (φ₀ ⁻ h) ∘ invEq ω ≡
        equivFun (α .fst) ∘ a ∘ (invEq ω) ∘ (φ₁ ⁻ equivFun (η .fst) h)
    equivariant a h = cong (λ - → equivFun (α .fst) ∘ a ∘ -) (comm h)
