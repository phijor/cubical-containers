module GpdCont.GroupAction.Product where

open import GpdCont.Prelude
open import GpdCont.HomotopySet using (_⊎Set_)
open import GpdCont.GroupAction.Base
open import GpdCont.Equiv using (equivΠCodComp)
open import GpdCont.Group.DirProd using (DirProd ; module DirProd)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base
import Cubical.Data.Sum as Sum


private
  variable
    ℓ : Level
    G H : Group ℓ
    X Y : hSet ℓ

open Action using (action ; pres·)

-- TOOD: This is wrong; it's the SUM of actions!
-- See GpdCont.GroupAction.Sum
_×Action_ : Action G X → Action H Y → Action (DirProd G H) (X ⊎Set Y)
σ ×Action τ = σ×τ where
  σ×τ : Action _ _
  σ×τ .action (g , h) = Sum.⊎-equiv (σ .action g) (τ .action h)
  σ×τ .pres· (g , h) (g′ , h′) = equivEq $ funExt λ where
    (Sum.inl x) → cong Sum.inl (funExt⁻ (cong equivFun (σ .pres· g g′)) x)
    (Sum.inr y) → cong Sum.inr (funExt⁻ (cong equivFun (τ .pres· h h′)) y)
