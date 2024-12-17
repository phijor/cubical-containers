module GpdCont.Group.DeloopingCategory where

open import GpdCont.Prelude
open import GpdCont.Categories.DisplayedOverContr using (∫ᶜ)

open import Cubical.Algebra.Group
open import Cubical.Data.Unit.Properties using (isContrUnit)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base

module _ {ℓ} (G : Group ℓ) where
  private
    open module G = GroupStr (str G) using (_·_)

  DeloopingCategory : Category _ _
  DeloopingCategory .Category.ob = Unit
  DeloopingCategory .Category.Hom[_,_] _ _ = ⟨ G ⟩
  DeloopingCategory .Category.id = G.1g
  DeloopingCategory .Category._⋆_ = G._·_
  DeloopingCategory .Category.⋆IdL = G.·IdL
  DeloopingCategory .Category.⋆IdR = G.·IdR
  DeloopingCategory .Category.⋆Assoc f g h = sym $ G.·Assoc f g h
  DeloopingCategory .Category.isSetHom = G.is-set

  ∫DeloopingCategory : ∀ {ℓo ℓh} → (D : Categoryᴰ DeloopingCategory ℓo ℓh) → Category ℓo (ℓ-max ℓ ℓh)
  ∫DeloopingCategory D = ∫ᶜ DeloopingCategory D isContrUnit
