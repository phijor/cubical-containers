module GpdCont.Prelude.Notation where

open import GpdCont.Prelude.Level
open import Cubical.Foundations.Prelude
import      Cubical.Foundations.Structure as Structure


record Underlying {ℓU} (U : Type ℓU) ℓ : Type (ℓ-max ℓU (ℓ-suc ℓ)) where
  field
    ⟨_⟩ : U → Type ℓ

private
  Type⟨_⟩ : ∀ {ℓ} (S : Type ℓ → Type ℓ) → Underlying (Structure.TypeWithStr ℓ S) ℓ
  Type⟨ S ⟩ .Underlying.⟨_⟩ = Structure.⟨_⟩ {S = S}

instance
  TypeWithStrUnderlying : ∀ {ℓ} {S : Type ℓ → Type ℓ} → Underlying (Structure.TypeWithStr ℓ S) ℓ
  TypeWithStrUnderlying {S = S} = Type⟨ S ⟩

module _ {ℓU ℓu ℓV ℓv ℓ} {U : Type ℓU} {V : Type ℓV} (u : Underlying U ℓu) (v : Underlying V ℓv) where
  private
    module u = Underlying u
    module v = Underlying v

  record FunLike (Fun : (x : U) → (y : V) → Type ℓ) : Type (ℓMax ℓ ℓU ℓu ℓV ℓv) where
    infixr 0 _#_
    field
      _#_ : ∀ {x y} → Fun x y → u.⟨ x ⟩ → v.⟨ y ⟩

open Underlying ⦃ ... ⦄ using (⟨_⟩) public

instance
  FunLikeTypeWithStr : ∀ {ℓ} {S : Type ℓ → Type ℓ} → FunLike Type⟨ S ⟩ Type⟨ S ⟩ (λ X Y → ⟨ X ⟩ → ⟨ Y ⟩)
  FunLikeTypeWithStr .FunLike._#_ f = f

open FunLike ⦃ ... ⦄ using (_#_) public

record Do {ℓ→ : Level → Level}  (M : ∀ {ℓ} → Type ℓ → Type (ℓ→ ℓ)) : Typeω where
  field
    _>>=_ : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → M A → (A → M B) → M B
    pure : ∀ {ℓ} {A : Type ℓ} → A → M A

open Do ⦃ ... ⦄ using (_>>=_ ; pure) public
