module GpdCont.TwoCategory.Pseudofunctor where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.LocalCategory
open import GpdCont.TwoCategory.LocalFunctor

open import Cubical.Categories.Category.Base using (isIso)
open import Cubical.Categories.Functor.Base using (_∘F_)
open import Cubical.Categories.NaturalTransformation.Base using (_≅ᶜ_ ; NatIso)
open import Cubical.Categories.Constructions.BinProduct using (_×F_)

module _ {ℓo ℓo′ ℓh ℓh′ ℓr ℓr′}
  {C : TwoCategory ℓo ℓh ℓr}
  {D : TwoCategory ℓo′ ℓh′ ℓr′}
  (F : LaxFunctor C D)
  where
    private
      module C = TwoCategory C
      module D = TwoCategory D
      module F = LaxFunctor F

      D[_,_] = LocalCategory D

    record isPseudoFunctor : Type (ℓ-max (ℓ-max ℓo ℓh) ℓr′) where
      field
        is-nat-iso-trans-lax : ∀ {x y z} (f : C.hom x y) (g : C.hom y z) → isIso D[ F.₀ x , F.₀ z ] (F.F-trans-lax f g)
        is-nat-iso-id-lax : ∀ (x : C.ob) → isIso D[ F.₀ x , F.₀ x ] (F.F-id-lax x)

      LaxFunctorialityIso : ∀ (x y z : C.ob) →
        compositionFunctor D (F.₀ x) (F.₀ y) (F.₀ z) ∘F (LocalFunctor F x y ×F LocalFunctor F y z)
          ≅ᶜ
        LocalFunctor F x z ∘F compositionFunctor C x y z
      LaxFunctorialityIso x y z .NatIso.trans = LaxFunctoriality F x y z
      LaxFunctorialityIso x y z .NatIso.nIso (f , g) = is-nat-iso-trans-lax f g

      LaxUnitalityIso : ∀ (x : C.ob) →
        identityFunctor D (F.₀ x)
          ≅ᶜ
        LocalFunctor F x x ∘F identityFunctor C x
      LaxUnitalityIso x .NatIso.trans = LaxUnitality F x
      LaxUnitalityIso x .NatIso.nIso _ = is-nat-iso-id-lax x
