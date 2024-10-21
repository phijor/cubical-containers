module GpdCont.TwoCategory.StructureOver where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

open import Cubical.WildCat.Base using (WildCat)

record TwoCategoryStrOver {ℓo ℓh} (C : WildCat ℓo ℓh) (ℓr : Level): Type (ℓ-max ℓo (ℓ-max ℓh (ℓ-suc ℓr))) where
  private
    open module C = WildCat C using (ob) renaming (Hom[_,_] to hom ; _⋆_ to _⋆₁_)

  field
    rel : {x y : ob} (f g : hom x y) → Type ℓr
    is-set-rel : {x y : ob} (f g : hom x y) → isSet (rel f g)

  field
    id-rel : {x y : ob} (f : hom x y) → rel f f

    trans : {x y : C.ob} {f g h : hom x y}
      → rel f g
      → rel g h
      ---------
      → rel f h

    comp-rel : {x y z : ob}
      → {f₁ f₂ : hom x y} {g₁ g₂ : hom y z}
      → (r : rel f₁ f₂)
      → (s : rel g₁ g₂)
      ---------------------------
      → rel (f₁ ⋆₁ g₁) (f₂ ⋆₁ g₂)

  -- field
  --   is-two-category : IsTwoCategory ob hom rel {! !}

  id-hom : (x : ob) → hom x x
  id-hom x = C.id {x}

  -- 🤡

  -- toTwoCategory : TwoCategory ℓo ℓh ℓr
  -- toTwoCategory .TwoCategory.ob = ob
  -- toTwoCategory .TwoCategory.hom = hom
  -- toTwoCategory .TwoCategory.rel = rel
  -- toTwoCategory .TwoCategory.two-category-structure = twoCatStr
  -- toTwoCategory .TwoCategory.is-two-category = isTwoCategory

module _ {ℓo ℓh} (C : WildCat ℓo ℓh) (ℓr : Level) (C₂ : TwoCategoryStrOver C ℓr) where
  private
    open module C = WildCat C using (ob) renaming (Hom[_,_] to hom ; _⋆_ to _⋆₁_)
    module C₂ = TwoCategoryStrOver C₂

  twoCategoryStr : TwoCategoryStr C.ob C.Hom[_,_] C₂.rel
  twoCategoryStr = record { C₂ }

  isTwoCategory : IsTwoCategory _ _ _ twoCategoryStr
  isTwoCategory = record { C₂ }
