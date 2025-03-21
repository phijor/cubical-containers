module GpdCont.Prelude.Notation where

open import Cubical.Foundations.Prelude
import      Cubical.Foundations.Structure as Structure


record Underlying {ℓU} (U : Type ℓU) ℓ : Type (ℓ-max ℓU (ℓ-suc ℓ)) where
  field
    ⟨_⟩ : U → Type ℓ

instance
  TypeWithStrUnderlying : ∀ {ℓ} {S : Type ℓ → Type ℓ} → Underlying (Structure.TypeWithStr ℓ S) ℓ
  TypeWithStrUnderlying {S} .Underlying.⟨_⟩ = Structure.⟨_⟩ {S = S}

module _ {ℓ ℓU} {U : Type ℓU} (u : Underlying U ℓ) where
  private
    module u = Underlying u

  record FunLike (H : (x y : U) → Type ℓ) : Type (ℓ-max ℓ ℓU) where
    field
      _#_ : ∀ {x y} → H x y → u.⟨ x ⟩ → u.⟨ y ⟩

open Underlying ⦃ ... ⦄ using (⟨_⟩) public

-- instance
--   FunLikeTypeWithStr : ∀ {ℓ} {S : Type ℓ → Type ℓ} → FunLike
