module GpdCont.GroupAction.Product where

open import GpdCont.Prelude
open import GpdCont.HomotopySet using (_⊎Set_)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Category
open import GpdCont.Group.DirProd as GroupDirProd using (module DirProd ; DirProd)

open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.MorphismProperties using (GroupHom≡)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.BinProduct

open import Cubical.Data.Sum as Sum using (⊎-equiv)

private
  module GroupAction ℓ = Category (GroupAction ℓ)

  variable
    ℓ : Level
    σ τ ω : GroupAction.ob ℓ

open Action

productAction : (σ τ : GroupAction.ob ℓ) → GroupAction.ob ℓ
productAction ((G , X) , σ) ((H , Y) , τ) = prod where
  G×H = DirProd G H

  σ×τ : Action G×H (X ⊎Set Y)
  σ×τ .action (g , h) = ⊎-equiv (σ .action g) (τ .action h)
  σ×τ .pres· (g₀ , h₀) (g₁ , h₁) = equivEq $ funExt λ where
    (Sum.inl x) → cong Sum.inl (funExt⁻ (cong equivFun (σ .pres· g₀ g₁)) x)
    (Sum.inr y) → cong Sum.inr (funExt⁻ (cong equivFun (τ .pres· h₀ h₁)) y)

  prod : GroupAction.ob _
  prod .fst .fst = G×H
  prod .fst .snd = X ⊎Set Y
  prod .snd = σ×τ

fstEquivariant : GroupAction ℓ [ productAction σ τ , σ ]
fstEquivariant {σ = σ@((G , _) , _)} {τ = τ@((H , _) , _)} = goal where
  goal : GroupAction _ [ productAction σ τ , σ ]
  goal .fst .fst = DirProd.fstHom G H
  goal .fst .snd = Sum.inl
  goal .snd _ = refl

sndEquivariant : GroupAction ℓ [ productAction σ τ , τ ]
sndEquivariant {σ = σ@((G , _) , _)} {τ = τ@((H , _) , _)} = goal where
  goal : GroupAction _ [ productAction σ τ , τ ]
  goal .fst .fst = DirProd.sndHom G H
  goal .fst .snd = Sum.inr
  goal .snd _ = refl

prodEquivariant : (f₁ : GroupAction ℓ [ ω , σ ]) (f₂ : GroupAction ℓ [ ω , τ ])
  → GroupAction ℓ [ ω , productAction σ τ ]
prodEquivariant {ω} {σ} {τ} f₁*@((φ₁ , f₁) , e₁) f₂*@((φ₂ , f₂) , e₂) = goal where
  goal : GroupAction _ [ ω , productAction σ τ ]
  goal .fst .fst = DirProd.pairingHom _ _ φ₁ φ₂
  goal .fst .snd = Sum.rec f₁ f₂
  goal .snd g = funExt λ where
    (Sum.inl x) → e₁ g ≡$ x
    (Sum.inr y) → e₂ g ≡$ y

GroupActionBinProducts : BinProducts (GroupAction ℓ)
GroupActionBinProducts σ τ = prod where
  prod : BinProduct _ _ _
  prod .BinProduct.binProdOb = productAction σ τ
  prod .BinProduct.binProdPr₁ = fstEquivariant {σ = σ} {τ = τ}
  prod .BinProduct.binProdPr₂ = sndEquivariant {σ = σ} {τ = τ}
  prod .BinProduct.univProp {z = ω} u v = univ where
    univ : ∃![ u×v ∈ GroupAction _ [ ω , productAction σ τ ] ] (u×v ⋆⟨ GroupAction _ ⟩ fstEquivariant ≡ u) × {! !}
    univ .fst = prodEquivariant u v , GroupActionHom≡ (≡-× (GroupHom≡ refl) {! !}) , {! !}
    univ .snd = {! !}
