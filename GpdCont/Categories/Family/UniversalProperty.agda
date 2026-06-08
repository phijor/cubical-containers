module GpdCont.Categories.Family.UniversalProperty where

open import GpdCont.Prelude
open import GpdCont.Prelude.Level

open import GpdCont.Categories.Family
open import GpdCont.Categories.Family.Elim
open import GpdCont.Categories.Coproducts using (Coproducts) renaming (module Notation to CoproductNotation)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Equivalence.Base

module _ {ℓo ℓh ℓo' ℓh'} (C : Category ℓo ℓh) (ΣC : Category ℓo' ℓh') where
  private
    module C = Category C
    module ΣC = Category ΣC

  record FamStr (ℓ : Level) : Type (ℓ-suc (ℓMax ℓ ℓo ℓh ℓo' ℓh')) where
    field
      coprod : Coproducts ΣC ℓ

    private
      module ∐C = CoproductNotation ΣC ℓ coprod

--       ι' : (x : C.ob) → (J : Type ℓ) → (y : J →  → (Σ[ j ∈ J ] C.Hom[ x , 

    field
      emb : Functor C ΣC
      emb-fully-faithful : Functor.isFullyFaithful emb
      -- emb-connected : (x : C.ob) → {! ∐C.ι !}

  FamStr→Equiv : ∀ {ℓ} → FamStr ℓ → Fam ℓ C ≃ᶜ ΣC
  FamStr→Equiv {ℓ} str = equiv where
    open FamStr str
    module ∐C = CoproductNotation ΣC ℓ coprod

    F : Functor (Fam _ C) ΣC
    F = Elim.elimFunctor coprod emb

    module F = Functor F

    ff : F.isFullyFaithful
    ff x*@(J , x) y*@(K , y) = {! F.F-hom {x = x*} {y = y*} !} where
      foo : Fam ℓ C [ (J , x) , (K , y) ] → ΣC [ F.F-ob (J , x) , F.F-ob (K , y) ]
      foo = F.F-hom {x = x*} {y = y*}

      foo-beta : ∀ f → foo f ≡ {!∐C.ι!}
      foo-beta f = refl

    equiv : Fam _ C ≃ᶜ ΣC
    equiv ._≃ᶜ_.func = F
    equiv ._≃ᶜ_.isEquiv = {! !}
