module GpdCont.Categories.LeftAdjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') (F : Functor C D) where
  LeftAdjointAt' : (d : D .ob) → Type _
  LeftAdjointAt' = RightAdjointAt' (C ^op) (D ^op) (F ^opF)

  LeftAdjoint' : Type _
  LeftAdjoint' = RightAdjoint' (C ^op) (D ^op) (F ^opF)
