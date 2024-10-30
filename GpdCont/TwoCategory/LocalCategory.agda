module GpdCont.TwoCategory.LocalCategory where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Pseudofunctor

open import Cubical.Categories.Category.Base

module _ {ℓo ℓh ℓr}
  (C : TwoCategory ℓo ℓh ℓr)
  (x y : TwoCategory.ob C)
  where
    private
      module C = TwoCategory C

    LocalCategory : Category ℓh ℓr
    LocalCategory .Category.ob = C.hom x y
    LocalCategory .Category.Hom[_,_] = C.rel
    LocalCategory .Category.id = C.id-rel _
    LocalCategory .Category._⋆_ = C.trans
    LocalCategory .Category.⋆IdL = C.trans-unit-left
    LocalCategory .Category.⋆IdR = C.trans-unit-right
    LocalCategory .Category.⋆Assoc = C.trans-assoc
    LocalCategory .Category.isSetHom = C.is-set-rel _ _
