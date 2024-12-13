module GpdCont.TwoCategory.Family.Functor where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.Displayed.LaxFunctor
open import GpdCont.TwoCategory.Family.Base
open import GpdCont.TwoCategory.HomotopySet using (SetEq ; isLocallyThinSetEq ; idSetEq)

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

  LiftFunctorᴰ : LaxFunctorᴰ (idSetEq ℓ) (Famᴰ C ℓ) (Famᴰ D ℓ)
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
