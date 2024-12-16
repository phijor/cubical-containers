open import GpdCont.Prelude hiding (_×_)

open import Cubical.Categories.Category.Base

module GpdCont.Categories.Products {ℓo ℓh} (C : Category ℓo ℓh) (ℓ : Level) where

open import GpdCont.HomotopySet as HSet
import      GpdCont.Categories.Diagonal as Diagonal

open import Cubical.Foundations.HLevels
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable

private
  module C where
    open Category C public
    open Diagonal C ℓ public


Product : (K : hSet ℓ) → (c : ⟨ K ⟩ → C.ob) → Type _
Product K = RightAdjointAt' _ _ (C.Δ K)

Products : Type _
Products = ∀ K → RightAdjoint' _ _ (C.Δ K)

module NotationAt (K : hSet ℓ) (c : ⟨ K ⟩ → C.ob) (ip : Product K c) where
  open UniversalElement ip

  Π : C.ob
  Π = vertex

module Notation (ip : Products) where
  open import Cubical.Data.Bool

  module _ K (c : ⟨ K ⟩ → C.ob) where open NotationAt K c (ip K c) public

  terminal : C.ob
  terminal = Π (EmptySet ℓ) λ ()

  _×_ : C.ob → C.ob → C.ob
  _×_ x y = Π (Bool* , isOfHLevelLift 2 isSetBool) (λ { b → if b .lower then x else y })
