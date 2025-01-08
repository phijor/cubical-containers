open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

module GpdCont.TwoCategory.Displayed.Unit
  {ℓo ℓh ℓr : Level}
  (C : TwoCategory ℓo ℓh ℓr)
  where

private
  module C = TwoCategory C

open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.StrictFunctor
open import GpdCont.TwoCategory.Displayed.Base
open import GpdCont.TwoCategory.Displayed.LaxFunctor
open import GpdCont.TwoCategory.Displayed.StrictFunctor

open import Cubical.Data.Unit using (Unit ; tt ; isOfHLevelUnit)

Unitᴰ : TwoCategoryᴰ C ℓ-zero ℓ-zero ℓ-zero
Unitᴰ .TwoCategoryᴰ.ob[_] _ = Unit
Unitᴰ .TwoCategoryᴰ.hom[_] _ _ _ = Unit
Unitᴰ .TwoCategoryᴰ.rel[_] _ _ _ = Unit
Unitᴰ .TwoCategoryᴰ.two-category-structureᴰ .TwoCategoryStrᴰ.id-homᴰ _ = tt
Unitᴰ .TwoCategoryᴰ.two-category-structureᴰ .TwoCategoryStrᴰ.comp-homᴰ _ _ = tt
Unitᴰ .TwoCategoryᴰ.two-category-structureᴰ .TwoCategoryStrᴰ.id-relᴰ _ = tt
Unitᴰ .TwoCategoryᴰ.two-category-structureᴰ .TwoCategoryStrᴰ.transᴰ _ _ = tt
Unitᴰ .TwoCategoryᴰ.two-category-structureᴰ .TwoCategoryStrᴰ.comp-relᴰ _ _ = tt
Unitᴰ .TwoCategoryᴰ.is-two-categoryᴰ .IsTwoCategoryᴰ.is-set-relᴰ _ _ = isOfHLevelUnit 2
Unitᴰ .TwoCategoryᴰ.is-two-categoryᴰ .IsTwoCategoryᴰ.trans-assocᴰ _ _ _ = refl
Unitᴰ .TwoCategoryᴰ.is-two-categoryᴰ .IsTwoCategoryᴰ.trans-unit-leftᴰ _ = refl
Unitᴰ .TwoCategoryᴰ.is-two-categoryᴰ .IsTwoCategoryᴰ.trans-unit-rightᴰ _ = refl
Unitᴰ .TwoCategoryᴰ.is-two-categoryᴰ .IsTwoCategoryᴰ.comp-rel-idᴰ _ _ = refl
Unitᴰ .TwoCategoryᴰ.is-two-categoryᴰ .IsTwoCategoryᴰ.comp-rel-transᴰ _ _ _ _ = refl
Unitᴰ .TwoCategoryᴰ.is-two-categoryᴰ .IsTwoCategoryᴰ.comp-hom-assocᴰ _ _ _ = refl
Unitᴰ .TwoCategoryᴰ.is-two-categoryᴰ .IsTwoCategoryᴰ.comp-hom-unit-leftᴰ _ = refl
Unitᴰ .TwoCategoryᴰ.is-two-categoryᴰ .IsTwoCategoryᴰ.comp-hom-unit-rightᴰ _ = refl
Unitᴰ .TwoCategoryᴰ.is-two-categoryᴰ .IsTwoCategoryᴰ.comp-rel-assocᴰ _ _ _ = refl
Unitᴰ .TwoCategoryᴰ.is-two-categoryᴰ .IsTwoCategoryᴰ.comp-rel-unit-leftᴰ _ = refl
Unitᴰ .TwoCategoryᴰ.is-two-categoryᴰ .IsTwoCategoryᴰ.comp-rel-unit-rightᴰ _ = refl

UnitOver : TwoCategory ℓo ℓh ℓr
UnitOver = TotalTwoCategory.∫ C Unitᴰ

ForgetUnit : LaxFunctor UnitOver C
ForgetUnit = TotalTwoCategory.Fst C Unitᴰ

AddUnit : StrictFunctor C UnitOver
AddUnit .StrictFunctor.F-ob = _, tt
AddUnit .StrictFunctor.F-hom =  _, tt
AddUnit .StrictFunctor.F-rel =  _, tt
AddUnit .StrictFunctor.F-rel-id = refl
AddUnit .StrictFunctor.F-rel-trans r s = refl
AddUnit .StrictFunctor.F-hom-comp f g = refl
AddUnit .StrictFunctor.F-hom-id x = refl
AddUnit .StrictFunctor.F-assoc-filler-left f g h .fst = refl
AddUnit .StrictFunctor.F-assoc-filler-left f g h .snd = reflSquare _
AddUnit .StrictFunctor.F-assoc-filler-right f g h .fst = refl
AddUnit .StrictFunctor.F-assoc-filler-right f g h .snd = reflSquare _
AddUnit .StrictFunctor.F-assoc f g h = λ i j → C.comp-hom-assoc f g h i , tt
AddUnit .StrictFunctor.F-unit-left-filler f .fst = refl
AddUnit .StrictFunctor.F-unit-left-filler f .snd = reflSquare _
AddUnit .StrictFunctor.F-unit-left f = λ i j → C.comp-hom-unit-left f i , tt
AddUnit .StrictFunctor.F-unit-right-filler f .fst = refl
AddUnit .StrictFunctor.F-unit-right-filler f .snd = reflSquare _
AddUnit .StrictFunctor.F-unit-right f = λ i j → C.comp-hom-unit-right f i , tt

module _
  {ℓo′ ℓh′ ℓr′ ℓoᴰ ℓhᴰ ℓrᴰ}
  {D : TwoCategory ℓo′ ℓh′ ℓr′}
  (F : StrictFunctor C D)
  {Dᴰ : TwoCategoryᴰ D ℓoᴰ ℓhᴰ ℓrᴰ}
  (Fᴰ : StrictFunctorᴰ F Unitᴰ Dᴰ)
  where

  private
    ∫D = TotalTwoCategory.∫ D Dᴰ

    module F = StrictFunctor F
    module Fᴰ = StrictFunctorᴰ Fᴰ

  ReindexUnit : StrictFunctor C ∫D
  ReindexUnit .StrictFunctor.F-ob x .fst = F.₀ x
  ReindexUnit .StrictFunctor.F-ob x .snd = Fᴰ.₀ tt
  ReindexUnit .StrictFunctor.F-hom f .fst = F.₁ f
  ReindexUnit .StrictFunctor.F-hom f .snd = Fᴰ.₁ tt
  ReindexUnit .StrictFunctor.F-rel r .fst = F.₂ r
  ReindexUnit .StrictFunctor.F-rel r .snd = Fᴰ.₂ tt
  ReindexUnit .StrictFunctor.F-rel-id {f = f} i .fst = F.F-rel-id {f = f} i
  ReindexUnit .StrictFunctor.F-rel-id {f = f} i .snd = Fᴰ.F-rel-idᴰ tt i
  ReindexUnit .StrictFunctor.F-rel-trans r s i .fst = F.F-rel-trans r s i
  ReindexUnit .StrictFunctor.F-rel-trans r s i .snd = Fᴰ.F-rel-transᴰ tt tt i
  ReindexUnit .StrictFunctor.F-hom-comp f g i .fst = F.F-hom-comp f g i
  ReindexUnit .StrictFunctor.F-hom-comp f g i .snd = Fᴰ.F-hom-compᴰ tt tt i
  ReindexUnit .StrictFunctor.F-hom-id x i .fst = F.F-hom-id x i
  ReindexUnit .StrictFunctor.F-hom-id x i .snd = Fᴰ.F-hom-idᴰ tt i
  ReindexUnit .StrictFunctor.F-assoc-filler-left f g h .fst i .fst = F.F-assoc-filler-left f g h .fst i
  ReindexUnit .StrictFunctor.F-assoc-filler-left f g h .fst i .snd = Fᴰ.F-assoc-filler-leftᴰ tt tt tt .fst i
  ReindexUnit .StrictFunctor.F-assoc-filler-left f g h .snd i j .fst = F.F-assoc-filler-left f g h .snd i j
  ReindexUnit .StrictFunctor.F-assoc-filler-left f g h .snd i j .snd = Fᴰ.F-assoc-filler-leftᴰ tt tt tt .snd i j
  ReindexUnit .StrictFunctor.F-assoc-filler-right f g h .fst i .fst = F.F-assoc-filler-right f g h .fst i
  ReindexUnit .StrictFunctor.F-assoc-filler-right f g h .fst i .snd = Fᴰ.F-assoc-filler-rightᴰ tt tt tt .fst i
  ReindexUnit .StrictFunctor.F-assoc-filler-right f g h .snd i j .fst = F.F-assoc-filler-right f g h .snd i j
  ReindexUnit .StrictFunctor.F-assoc-filler-right f g h .snd i j .snd = Fᴰ.F-assoc-filler-rightᴰ tt tt tt .snd i j
  ReindexUnit .StrictFunctor.F-assoc f g h i j .fst = F.F-assoc f g h i j
  ReindexUnit .StrictFunctor.F-assoc f g h i j .snd = Fᴰ.F-assocᴰ tt tt tt i j
  ReindexUnit .StrictFunctor.F-unit-left-filler f .fst i .fst = F.F-unit-left-filler f .fst i
  ReindexUnit .StrictFunctor.F-unit-left-filler f .fst i .snd = Fᴰ.F-unit-left-fillerᴰ tt .fst i
  ReindexUnit .StrictFunctor.F-unit-left-filler f .snd i j .fst = F.F-unit-left-filler f .snd i j
  ReindexUnit .StrictFunctor.F-unit-left-filler f .snd i j .snd = Fᴰ.F-unit-left-fillerᴰ tt .snd i j
  ReindexUnit .StrictFunctor.F-unit-left f i j .fst = F.F-unit-left f i j
  ReindexUnit .StrictFunctor.F-unit-left f i j .snd = Fᴰ.F-unit-leftᴰ tt i j
  ReindexUnit .StrictFunctor.F-unit-right-filler f .fst i .fst = F.F-unit-right-filler f .fst i
  ReindexUnit .StrictFunctor.F-unit-right-filler f .fst i .snd = Fᴰ.F-unit-right-fillerᴰ tt .fst i
  ReindexUnit .StrictFunctor.F-unit-right-filler f .snd i j .fst = F.F-unit-right-filler f .snd i j
  ReindexUnit .StrictFunctor.F-unit-right-filler f .snd i j .snd = Fᴰ.F-unit-right-fillerᴰ tt .snd i j
  ReindexUnit .StrictFunctor.F-unit-right f i j .fst = F.F-unit-right f i j
  ReindexUnit .StrictFunctor.F-unit-right f i j .snd = Fᴰ.F-unit-rightᴰ tt i j
