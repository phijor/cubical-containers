module GpdCont.WildCat.FunctorCategory where

open import GpdCont.Prelude renaming (id to idfun)

open import Cubical.Foundations.Function using (flip) renaming (_∘_ to _∘fun_)
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.Base using (WildCat)
open import Cubical.WildCat.Functor as Functor using (WildFunctor ; WildNatTrans)

private
  variable
    ℓCo ℓCh ℓDo ℓDh : Level

module _ (C : WildCat ℓCo ℓCh) (D : WildCat ℓDo ℓDh) where
  private
    ℓ = ℓ-max (ℓ-max ℓCo ℓCh) (ℓ-max ℓDo ℓDh)

    module D = WildCat D

    _⋆nat_ : ∀ {F G H : WildFunctor C D} → WildNatTrans _ _ F G → WildNatTrans _ _ G H → WildNatTrans _ _ F H
    _⋆nat_ = Functor.compWildNatTrans _ _ _

  idNatTrans : (F : WildFunctor C D) → WildNatTrans _ _ F F
  idNatTrans F .WildNatTrans.N-ob _ = D.id
  idNatTrans F .WildNatTrans.N-hom f = D.⋆IdR (F-hom f) ∙ sym (D.⋆IdL (F-hom f))
    where
      open WildFunctor F using (F-hom)

  -- idNatTransᵣ : ∀ {F G : WildFunctor C D} (α : WildNatTrans _ _ F G) → α ⋆nat idNatTrans G ≡ α
  -- idNatTransᵣ α i .WildNatTrans.N-ob x = D.⋆IdR (α .WildNatTrans.N-ob x) i
  -- idNatTransᵣ α i .WildNatTrans.N-hom f = {! !}

  -- FunctorCat : WildCat ℓ ℓ
  -- FunctorCat .WildCat.ob = WildFunctor C D
  -- FunctorCat .WildCat.Hom[_,_] = WildNatTrans C D
  -- FunctorCat .WildCat.id = idNatTrans _
  -- FunctorCat .WildCat._⋆_ = Functor.compWildNatTrans _ _ _
  -- FunctorCat .WildCat.⋆IdL = {! !}
  -- FunctorCat .WildCat.⋆IdR = {! !}
  -- FunctorCat .WildCat.⋆Assoc = {! !}
