open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

module GpdCont.TwoCategory.Displayed.Unit
  {ℓo ℓh ℓr : Level}
  (C : TwoCategory ℓo ℓh ℓr)
  where

private
  module C = TwoCategory C

open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.Displayed.Base
open import GpdCont.TwoCategory.Displayed.LaxFunctor

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

AddUnit : LaxFunctor C UnitOver
AddUnit .LaxFunctor.F-ob = _, tt
AddUnit .LaxFunctor.F-hom = _, tt
AddUnit .LaxFunctor.F-rel = _, tt
AddUnit .LaxFunctor.F-rel-id = refl
AddUnit .LaxFunctor.F-rel-trans r s = refl
AddUnit .LaxFunctor.F-trans-lax f g .fst = C.id-rel (C.comp-hom f g)
AddUnit .LaxFunctor.F-trans-lax f g .snd = tt
AddUnit .LaxFunctor.F-trans-lax-natural r s i .fst = (C.trans-unit-right (C.comp-rel r s) ∙ (sym $ C.trans-unit-left _)) i
AddUnit .LaxFunctor.F-trans-lax-natural r s i .snd = tt
AddUnit .LaxFunctor.F-id-lax x = C.id-rel (C.id-hom x) , tt
AddUnit .LaxFunctor.F-assoc f g h i .fst = {! !}
AddUnit .LaxFunctor.F-assoc f g h i .snd = tt
AddUnit .LaxFunctor.F-unit-left = {! !}
AddUnit .LaxFunctor.F-unit-right = {! !}

ReindexUnit : ∀ {ℓo′ ℓh′ ℓr′ ℓoᴰ ℓhᴰ ℓrᴰ} (D : TwoCategory ℓo′ ℓh′ ℓr′)  (F : LaxFunctor C D)
  → (Dᴰ : TwoCategoryᴰ D ℓoᴰ ℓhᴰ ℓrᴰ)
  → LaxFunctorᴰ F Unitᴰ Dᴰ
  → LaxFunctor C (TotalTwoCategory.∫ D Dᴰ)
ReindexUnit D F Dᴰ Fᴰ = F′ where
  module F = LaxFunctor F
  module Fᴰ = LaxFunctorᴰ Fᴰ
  F′ : LaxFunctor C (TotalTwoCategory.∫ D Dᴰ)
  F′ .LaxFunctor.F-ob x = F.₀ x , Fᴰ.₀ tt
  F′ .LaxFunctor.F-hom f = F.₁ f , Fᴰ.₁ tt
  F′ .LaxFunctor.F-rel r = F.₂  r , Fᴰ.₂ tt
  F′ .LaxFunctor.F-rel-id i = F.F-rel-id i , Fᴰ.F-rel-idᴰ i
  F′ .LaxFunctor.F-rel-trans r s i .fst = F.F-rel-trans r s i
  F′ .LaxFunctor.F-rel-trans r s i .snd = Fᴰ.F-rel-transᴰ tt tt i
  F′ .LaxFunctor.F-trans-lax f g .fst = F.F-trans-lax f g
  F′ .LaxFunctor.F-trans-lax f g .snd = Fᴰ.F-trans-laxᴰ tt tt
  F′ .LaxFunctor.F-trans-lax-natural r s i .fst = {! !}
  F′ .LaxFunctor.F-trans-lax-natural r s i .snd = {! !}
  F′ .LaxFunctor.F-id-lax x = {! !}
  F′ .LaxFunctor.F-assoc f g h i .fst = F.F-assoc f g h i
  F′ .LaxFunctor.F-assoc f g h i .snd = Fᴰ.F-assocᴰ tt tt tt i
  F′ .LaxFunctor.F-unit-left = {! !}
  F′ .LaxFunctor.F-unit-right = {! !}
