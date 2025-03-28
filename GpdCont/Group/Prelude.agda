module GpdCont.Group.Prelude where

open import GpdCont.Prelude.Level
open import GpdCont.Prelude.Notation public

import      Cubical.Foundations.Structure as Structure
open import Cubical.Data.Sigma.Base
open import Cubical.Algebra.Group.Base public
open import Cubical.Algebra.Group.Morphisms public

instance
  GroupUnderlying : ∀ {ℓ} → Underlying (Group ℓ) ℓ
  GroupUnderlying .Underlying.⟨_⟩ = Structure.⟨_⟩

instance
  GroupHomFunLike : ∀ {ℓG ℓH} → FunLike (GroupUnderlying {ℓG}) (GroupUnderlying {ℓH}) GroupHom
  GroupHomFunLike .FunLike._#_ = fst
