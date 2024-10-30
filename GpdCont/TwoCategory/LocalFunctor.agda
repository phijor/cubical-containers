module GpdCont.TwoCategory.LocalFunctor where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Pseudofunctor
open import GpdCont.TwoCategory.LocalCategory

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base

module _ {ℓo ℓo′ ℓh ℓh′ ℓr ℓr′}
  {C : TwoCategory ℓo ℓh ℓr}
  {D : TwoCategory ℓo′ ℓh′ ℓr′}
  (F : LaxFunctor C D)
  where
    private
      ℓ = ℓ-max (ℓ-max ℓo (ℓ-max ℓh ℓr)) (ℓ-max ℓo′ (ℓ-max ℓh′ ℓr′))
      module C = TwoCategory C
      module D = TwoCategory D
      module F = LaxFunctor F

      C[_,_] = LocalCategory C
      D[_,_] = LocalCategory D

    LocalFunctor : (x y : C.ob) → Functor C[ x , y ] D[ F.₀ x , F.₀ y ]
    LocalFunctor x y .Functor.F-ob = F.₁
    LocalFunctor x y .Functor.F-hom = F.₂
    LocalFunctor x y .Functor.F-id = F.F-rel-id
    LocalFunctor x y .Functor.F-seq = F.F-rel-trans

    Locally : ∀ {ℓ} (P : ∀ {C : Category ℓh ℓr} {D : Category ℓh′ ℓr′} → Functor C D → Type ℓ) → Type _
    Locally P = ∀ (x y : C.ob) → P (LocalFunctor x y)
