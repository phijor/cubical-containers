module GpdCont.TwoCategory.Family.Functor where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.Displayed.LaxFunctor
open import GpdCont.TwoCategory.Family.Base
open import GpdCont.TwoCategory.HomotopySet using (SetEq ; isLocallyThinSetEq)

open import Cubical.Functions.FunExtEquiv
import      Cubical.Data.Equality as Eq

module _
  {ℓo ℓh ℓr ℓo′ ℓh′ ℓr′}
  {C : TwoCategory ℓo ℓh ℓr}
  {D : TwoCategory ℓo′ ℓh′ ℓr′}
  (F : LaxFunctor C D)
  (ℓ : Level)
  where

  private
    module F = LaxFunctor F
    module SetEq = TwoCategory (SetEq ℓ)

  idSet : LaxFunctor (SetEq ℓ) (SetEq ℓ)
  idSet .LaxFunctor.F-ob = id _
  idSet .LaxFunctor.F-hom = id _
  idSet .LaxFunctor.F-rel = id _
  idSet .LaxFunctor.F-rel-id = refl
  idSet .LaxFunctor.F-rel-trans _ _ = refl
  idSet .LaxFunctor.F-trans-lax _ _ = Eq.refl
  idSet .LaxFunctor.F-trans-lax-natural Eq.refl Eq.refl = refl
  idSet .LaxFunctor.F-id-lax x = Eq.refl
  idSet .LaxFunctor.F-assoc {x} {w} f g h = refl
  idSet .LaxFunctor.F-unit-left {x} {y} f = refl
  idSet .LaxFunctor.F-unit-right {x} {y} f = refl

  LiftFunctorᴰ : LaxFunctorᴰ idSet (Famᴰ C ℓ) (Famᴰ D ℓ)
  LiftFunctorᴰ .LaxFunctorᴰ.F-obᴰ xᴰ = F.₀ ∘ xᴰ
  LiftFunctorᴰ .LaxFunctorᴰ.F-homᴰ fᴰ = F.₁ ∘ fᴰ
  LiftFunctorᴰ .LaxFunctorᴰ.F-relᴰ {r = Eq.refl} rᴰ = F.₂ ∘ rᴰ
  LiftFunctorᴰ .LaxFunctorᴰ.F-rel-idᴰ {fᴰ} i j = F.F-rel-id {f = fᴰ j} i
  LiftFunctorᴰ .LaxFunctorᴰ.F-rel-transᴰ {r = Eq.refl} {s = Eq.refl} rᴰ sᴰ i j = F.F-rel-trans (rᴰ j) (sᴰ j) i
  LiftFunctorᴰ .LaxFunctorᴰ.F-trans-laxᴰ fᴰ gᴰ = λ j → F.F-trans-lax (fᴰ j) (gᴰ _)
  LiftFunctorᴰ .LaxFunctorᴰ.F-trans-lax-naturalᴰ {r = Eq.refl} {s = Eq.refl} rᴰ sᴰ i j = F.F-trans-lax-natural (rᴰ j) (sᴰ _) i
  LiftFunctorᴰ .LaxFunctorᴰ.F-id-laxᴰ xᴰ = F.F-id-lax ∘ xᴰ
  LiftFunctorᴰ .LaxFunctorᴰ.F-assocᴰ fᴰ gᴰ hᴰ i j = F.F-assoc (fᴰ j) (gᴰ _) (hᴰ _) i
  LiftFunctorᴰ .LaxFunctorᴰ.F-unit-leftᴰ fᴰ i j = F.F-unit-left (fᴰ j) i
  LiftFunctorᴰ .LaxFunctorᴰ.F-unit-rightᴰ fᴰ i j = F.F-unit-right (fᴰ j) i

  LiftFunctor : LaxFunctor (Fam C ℓ) (Fam D ℓ)
  LiftFunctor = LaxFunctorᴰ.toTotalFunctor LiftFunctorᴰ
