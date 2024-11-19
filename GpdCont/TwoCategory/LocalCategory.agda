module GpdCont.TwoCategory.LocalCategory where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Terminal using (TerminalCategory ; FunctorFromTerminal)
open import Cubical.Categories.Constructions.BinProduct using (_×C_)

module _ {ℓo ℓh ℓr}
  (C : TwoCategory ℓo ℓh ℓr)
  where
    private
      module C = TwoCategory C

    isLocallyStrict : Type (ℓ-max ℓo ℓh)
    isLocallyStrict = ∀ x y → isSet (C.hom x y)

    module _ (x y : TwoCategory.ob C) where
      LocalCategory :  Category ℓh ℓr
      LocalCategory .Category.ob = C.hom x y
      LocalCategory .Category.Hom[_,_] = C.rel
      LocalCategory .Category.id = C.id-rel _
      LocalCategory .Category._⋆_ = C.trans
      LocalCategory .Category.⋆IdL = C.trans-unit-left
      LocalCategory .Category.⋆IdR = C.trans-unit-right
      LocalCategory .Category.⋆Assoc = C.trans-assoc
      LocalCategory .Category.isSetHom = C.is-set-rel _ _

    LocalCatIso : ∀ {x y : C.ob} (f g : C.hom x y) → Type _
    LocalCatIso {x} {y} f g = CatIso (LocalCategory x y) f g

    isSetLocalCatIso : ∀ {x y : C.ob} (f g : C.hom x y) → isSet (LocalCatIso f g)
    isSetLocalCatIso {x} {y} f g = isSet-CatIso {C = LocalCategory x y} f g

    identityFunctor : ∀ (x : C.ob) → Functor (TerminalCategory {ℓ-zero}) (LocalCategory x x)
    identityFunctor x = FunctorFromTerminal (C.id-hom x)

    compositionFunctor : (x y z : C.ob) → Functor (LocalCategory x y ×C LocalCategory y z) (LocalCategory x z)
    compositionFunctor x y z .Functor.F-ob (f , g) = C.comp-hom f g
    compositionFunctor x y z .Functor.F-hom (r , s) = C.comp-rel r s
    compositionFunctor x y z .Functor.F-id = sym $ C.comp-rel-id _ _
    compositionFunctor x y z .Functor.F-seq (r , s) (r′ , s′) = C.comp-rel-trans r r′ s s′
