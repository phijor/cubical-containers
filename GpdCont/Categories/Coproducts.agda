open import GpdCont.Prelude

open import Cubical.Categories.Category.Base

module GpdCont.Categories.Coproducts {ℓo ℓh} (C : Category ℓo ℓh) (ℓ : Level) where

open import GpdCont.HomotopySet as HSet
import      GpdCont.Categories.Diagonal as Diagonal
open import GpdCont.Categories.LeftAdjoint using (LeftAdjointAt' ; LeftAdjoint')

open import Cubical.Foundations.HLevels
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable

private
  module C where
    open Category C public
    open Diagonal C ℓ public


Coproduct : (K : hSet ℓ) → (c : ⟨ K ⟩ → C.ob) → Type _
Coproduct K = LeftAdjointAt' _ _ (C.Δ K)

Coproducts : Type _
Coproducts = ∀ K → LeftAdjoint' _ _ (C.Δ K)

module NotationAt (K : hSet ℓ) (c : ⟨ K ⟩ → C.ob) (p : Coproduct K c) where
  open UniversalElement p

  ⨆ : C.ob
  ⨆ = vertex

module Notation (p : Coproducts) where
  open import Cubical.Data.Bool

  module _ K (c : ⟨ K ⟩ → C.ob) where open NotationAt K c (p K c) public

  initial : C.ob
  initial = ⨆ (EmptySet ℓ) λ ()

  _⊔_ : C.ob → C.ob → C.ob
  _⊔_ x y = ⨆ (Bool* , isOfHLevelLift 2 isSetBool) (λ { b → if b .lower then x else y })
