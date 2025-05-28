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
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)


module _ {ℓ} (Ω : hSet ℓ) (A : Group ℓ) (H : Group ℓ) (φ : Action H Ω) where
  private
    ΠA : Group ℓ
    ΠA = ΠGroup {X = ⟨ Ω ⟩} (const A)

    ΠASet : hSet ℓ
    ΠASet .fst = ⟨ ΠA ⟩
    ΠASet .snd = str ΠA .GroupStr.is-set

    module H = GroupStr (str H)
    module φ where
      open Action φ public
      open ActionProperties φ public


    φ* : Action H ΠASet
    φ* .Action.action h = equivΠDomain (invEquiv (φ.action h))
    φ* .Action.pres· h h′ = equivEq (funExt₂ goal) where
      φ⁻ : ⟨ H ⟩ → ⟨ Ω ⟩ → ⟨ Ω ⟩
      φ⁻ = invEq ∘ φ.action

      goal : (as : ⟨ Ω ⟩ → ⟨ A ⟩) (ω : ⟨ Ω ⟩) → as (φ⁻ (h H.· h′) ω) ≡ as (φ⁻ h (φ⁻ h′ ω))
      goal as ω = cong as $
        (φ⁻ (h H.· h′) ω) ≡⟨ φ.action-inv-comp h h′ ≡$ ω ⟩
        (φ⁻ h (φ⁻ h′ ω)) ∎

  Wreath : Group ℓ
  Wreath = SemidirProd ΠA H φ*
