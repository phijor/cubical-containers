module GpdCont.Categories.Functor where

open import GpdCont.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base

private
  variable
    ℓo ℓh : Level
    C D : Category ℓo ℓh
    F : Functor C D

isSplitEssentiallySurjective : Functor C D → Type _
isSplitEssentiallySurjective {C} {D} F = (d : D .ob) → Σ[ c ∈ C .ob ] CatIso D (F .F-ob c) d where
  open Category
  open Functor

isSplitEssentiallySurjective→isEssentiallySurj : isSplitEssentiallySurjective F → Functor.isEssentiallySurj F
isSplitEssentiallySurjective→isEssentiallySurj = Σ→∃ ∘_

module _ {ℓo ℓh ℓo' ℓh'} {C : Category ℓo ℓh} {D : Category ℓo' ℓh'}
  {F : Functor C D}
  where
  private
    module D = Category D
    module C = Category C
    module F = Functor F

  isFullyFaithful→IsoEquiv : Functor.isFullyFaithful F → ∀ x y → {! !}
  isFullyFaithful→IsoEquiv = {! !}

  isFullyFaithful→isUnivalent : isUnivalent D → Functor.isFullyFaithful F → isUnivalent C
  isFullyFaithful→isUnivalent univ-D is-ff-F = goal where
    path-equiv : (x y : C.ob) → (x ≡ y) ≃ CatIso C x y
    path-equiv x y =
      (x ≡ y) ≃⟨ {! !} ⟩
      (F.F-ob x ≡ F.F-ob y) ≃⟨ {! !} ⟩
      CatIso C x y ≃∎

    goal : isUnivalent C
    goal .isUnivalent.univ x y = {! !}
