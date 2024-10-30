module GpdCont.TwoCategory.LocalFunctor where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.LocalCategory

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.BinProduct using (_×F_)
open import Cubical.Categories.Instances.Terminal using (TerminalCategory)

module _ {ℓo ℓo′ ℓh ℓh′ ℓr ℓr′}
  {C : TwoCategory ℓo ℓh ℓr}
  {D : TwoCategory ℓo′ ℓh′ ℓr′}
  (F : LaxFunctor C D)
  where
    private
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

    LaxFunctoriality : (x y z : C.ob) →
      compositionFunctor D (F.₀ x) (F.₀ y) (F.₀ z) ∘F (LocalFunctor x y ×F LocalFunctor y z)
        ⇒
      LocalFunctor x z ∘F compositionFunctor C x y z
    LaxFunctoriality x y z .NatTrans.N-ob (f , g) = F.F-trans-lax f g
    LaxFunctoriality x y z .NatTrans.N-hom (r , s) = F.F-trans-lax-natural r s

    LaxUnitality : ∀ (x : C.ob) →
      identityFunctor D (F.₀ x)
        ⇒
      LocalFunctor x x ∘F identityFunctor C x
    LaxUnitality x .NatTrans.N-ob _ = F.F-id-lax x
    LaxUnitality x .NatTrans.N-hom _ = goal where
      goal : D.id-rel _ D.∙ᵥ F.F-id-lax x ≡ (F.F-id-lax x) D.∙ᵥ (F.F-rel (C.id-rel _))
      goal = D.trans-unit-left _ ∙∙ sym (D.trans-unit-right _) ∙∙ cong (F.F-id-lax x D.∙ᵥ_) (sym F.F-rel-id)
