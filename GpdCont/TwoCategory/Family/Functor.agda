module GpdCont.TwoCategory.Family.Functor where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.StrictFunctor
open import GpdCont.TwoCategory.Displayed.StrictFunctor
open import GpdCont.TwoCategory.Family.Base
open import GpdCont.TwoCategory.HomotopySet using (SetEq)

import      Cubical.Data.Equality as Eq

module _
  {ℓo ℓh ℓr ℓo′ ℓh′ ℓr′}
  {C : TwoCategory ℓo ℓh ℓr}
  {D : TwoCategory ℓo′ ℓh′ ℓr′}
  (F : StrictFunctor C D)
  (ℓ : Level)
  where

  private
    module F = StrictFunctor F
    module SetEq = TwoCategory (SetEq ℓ)

  FamFunctorᴰ : StrictFunctorᴰ (idStrictFunctor (SetEq ℓ)) (Famᴰ C ℓ) (Famᴰ D ℓ)
  FamFunctorᴰ .StrictFunctorᴰ.F-obᴰ xᴰ = F.₀ ∘ xᴰ
  FamFunctorᴰ .StrictFunctorᴰ.F-homᴰ fᴰ = F.₁ ∘ fᴰ
  FamFunctorᴰ .StrictFunctorᴰ.F-relᴰ {r = Eq.refl} rᴰ = F.₂ ∘ rᴰ
  FamFunctorᴰ .StrictFunctorᴰ.F-rel-idᴰ fᴰ = funExt λ j → F.F-rel-id {f = fᴰ j}
  FamFunctorᴰ .StrictFunctorᴰ.F-rel-transᴰ {r = Eq.refl} {s = Eq.refl} rᴰ sᴰ = funExt λ j → F.F-rel-trans (rᴰ j) (sᴰ j)
  FamFunctorᴰ .StrictFunctorᴰ.F-hom-compᴰ {f} fᴰ gᴰ = funExt λ j → F.F-hom-comp (fᴰ j) (gᴰ (f j))
  FamFunctorᴰ .StrictFunctorᴰ.F-hom-idᴰ xᴰ = funExt λ j → F.F-hom-id (xᴰ j)
  FamFunctorᴰ .StrictFunctorᴰ.F-assoc-filler-leftᴰ fᴰ gᴰ hᴰ .fst = funExt λ j → F.F-assoc-filler-left (fᴰ j) (gᴰ _) (hᴰ _) .fst
  FamFunctorᴰ .StrictFunctorᴰ.F-assoc-filler-leftᴰ fᴰ gᴰ hᴰ .snd = funExtSquare λ j → F.F-assoc-filler-left (fᴰ j) (gᴰ _) (hᴰ _) .snd
  FamFunctorᴰ .StrictFunctorᴰ.F-assoc-filler-rightᴰ fᴰ gᴰ hᴰ .fst = funExt λ j → F.F-assoc-filler-right (fᴰ j) (gᴰ _) (hᴰ _) .fst
  FamFunctorᴰ .StrictFunctorᴰ.F-assoc-filler-rightᴰ fᴰ gᴰ hᴰ .snd = funExtSquare λ j → F.F-assoc-filler-right (fᴰ j) (gᴰ _) (hᴰ _) .snd
  FamFunctorᴰ .StrictFunctorᴰ.F-assocᴰ fᴰ gᴰ hᴰ = funExtSquare λ j → F.F-assoc (fᴰ j) (gᴰ _) (hᴰ _)
  FamFunctorᴰ .StrictFunctorᴰ.F-unit-left-fillerᴰ fᴰ .fst = funExt λ j → F.F-unit-left-filler (fᴰ j) .fst
  FamFunctorᴰ .StrictFunctorᴰ.F-unit-left-fillerᴰ fᴰ .snd = funExtSquare λ j → F.F-unit-left-filler (fᴰ j) .snd
  FamFunctorᴰ .StrictFunctorᴰ.F-unit-leftᴰ fᴰ = funExtSquare λ j → F.F-unit-left (fᴰ j)
  FamFunctorᴰ .StrictFunctorᴰ.F-unit-right-fillerᴰ fᴰ .fst = funExt λ j → F.F-unit-right-filler (fᴰ j) .fst
  FamFunctorᴰ .StrictFunctorᴰ.F-unit-right-fillerᴰ fᴰ .snd = funExtSquare λ j → F.F-unit-right-filler (fᴰ j) .snd
  FamFunctorᴰ .StrictFunctorᴰ.F-unit-rightᴰ fᴰ = funExtSquare λ j → F.F-unit-right (fᴰ j)

  FamFunctor : StrictFunctor (Fam C ℓ) (Fam D ℓ)
  FamFunctor = StrictFunctorᴰ.toTotalFunctor FamFunctorᴰ
