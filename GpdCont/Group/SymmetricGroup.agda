module GpdCont.Group.SymmetricGroup where

open import GpdCont.Prelude hiding (_▷_)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

import Cubical.Algebra.SymmetricGroup as SymmetricGroup

𝔖 : ∀ {ℓ} (X : hSet ℓ) → Group ℓ
𝔖 (X , is-set-X) = SymmetricGroup.SymGroup X is-set-X

module _ {ℓX ℓY} (X : hSet ℓX) (Y : hSet ℓY) where
  private
    module 𝔖X = GroupStr (str $ 𝔖 X)
    module 𝔖Y = GroupStr (str $ 𝔖 Y)

  symmConjEquiv : ⟨ X ⟩ ≃ ⟨ Y ⟩ → ⟨ 𝔖 X ⟩ ≃ ⟨ 𝔖 Y ⟩
  symmConjEquiv e = equivComp e e

  _ : (e : ⟨ X ⟩ ≃ ⟨ Y ⟩) → equivFun (symmConjEquiv e) ≡ (λ - → invEquiv e ∙ₑ - ∙ₑ e)
  _ = λ e → funExt λ α → equivEq refl

  opaque
    isGroupHomSymmConjEquiv : (e : ⟨ X ⟩ ≃ ⟨ Y ⟩) → IsGroupHom (str $ 𝔖 X) (equivFun (symmConjEquiv e)) (str $ 𝔖 Y)
    isGroupHomSymmConjEquiv (e , e-equiv) = makeIsGroupHom λ (α , _) (β , _) → equivEq $
      the (e⁻ ⋆ α ⋆ β ⋆ e ≡ e⁻ ⋆ α ⋆ e ⋆ e⁻ ⋆ β ⋆ e)
        λ i → e⁻ ⋆ α ⋆ (λ x → retIsEq e-equiv x (~ i)) ⋆ β ⋆ e
      where
        e⁻ : ⟨ Y ⟩ → ⟨ X ⟩
        e⁻ = invIsEq e-equiv

  symmConjGroupEquiv : ⟨ X ⟩ ≃ ⟨ Y ⟩ → GroupEquiv (𝔖 X) (𝔖 Y)
  symmConjGroupEquiv e .fst = symmConjEquiv e
  symmConjGroupEquiv e .snd = isGroupHomSymmConjEquiv e

  {-
  symmConjEquivUnique : (e f : ⟨ X ⟩ ≃ ⟨ Y ⟩) → symmConjEquiv e ≡ symmConjEquiv f
  symmConjEquivUnique (e , e-equiv) (f , f-equiv) = equivEq $ funExt λ { (α , _) → equivEq {!  !} }

  mereSymmConjEquiv : ∥ ⟨ X ⟩ ≃ ⟨ Y ⟩ ∥₁ → ⟨ 𝔖 X ⟩ ≃ ⟨ 𝔖 Y ⟩
  mereSymmConjEquiv = PT.rec→Set (isOfHLevel≃ 2 𝔖X.is-set 𝔖Y.is-set) symmConjEquiv symmConjEquivUnique
  -}
