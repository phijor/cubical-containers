module GpdCont.TwoCategory.GroupoidEnriched where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

open import Cubical.WildCat.Base using (WildCat)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.BinProduct using (_×C_)

{-
module _ {ℓo ℓh} (C : Category ℓo ℓh) where
  private
    module C = Category C

  module _ {ℓr}
    (E : {x y : C.ob} (f g : C [ x , y ]) → Type ℓr)
    (E-cat-str : (x y : C.ob) → CategoryStr (C [ x , y ]) (E {x} {y}))
    (let E[_,_] = λ (x y : C.ob) → CategoryStr.toCategory (E-cat-str x y))
    (let module E-cat x y = Category E[ x , y ])
    (E-hcomp : {x y z : C.ob} → Functor (E[ x , y ] ×C E[ y , z ]) E[ x , z ])
    where
      private
        module E {x} {y} = CategoryStr (E-cat-str x y)

      fromCatEnrichtment : TwoCategory ℓo ℓh ℓr
      fromCatEnrichtment .TwoCategory.ob = C.ob
      fromCatEnrichtment .TwoCategory.hom = C.Hom[_,_]
      fromCatEnrichtment .TwoCategory.rel = E
      fromCatEnrichtment .TwoCategory.two-category-structure = cat-str where
        cat-str : TwoCategoryStr _ _ _
        cat-str .TwoCategoryStr.id-hom x = C.id
        cat-str .TwoCategoryStr.comp-hom = C._⋆_
        cat-str .TwoCategoryStr.id-rel f = E.id-hom f
        cat-str .TwoCategoryStr.trans f g = E.comp-hom f g
        cat-str .TwoCategoryStr.comp-rel {f₁} {f₂} {g₁} {g₂} r s = {!E-hcomp .Functor.F-ob !}
      fromCatEnrichtment .TwoCategory.is-two-category = is-cat where
        open IsTwoCategory
        is-cat : IsTwoCategory _ _ _ _
        is-cat .is-set-rel f g = E.is-set-hom
        is-cat .trans-assoc = E.comp-hom-assoc
        is-cat .trans-unit-left = E.comp-hom-id-left
        is-cat .trans-unit-right = E.comp-hom-id-right
        is-cat .comp-rel-id = {! !}
        is-cat .comp-rel-trans = {! !}
        is-cat .comp-hom-assoc = {! !}
        is-cat .comp-hom-unit-left = {! !}
        is-cat .comp-hom-unit-right = {! !}
        is-cat .comp-rel-assoc = {! !}
        is-cat .comp-rel-unit-left = {! !}
        is-cat .comp-rel-unit-right = {! !}
        -}
