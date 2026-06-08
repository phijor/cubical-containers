open import GpdCont.Prelude

module GpdCont.ActionContainer.AsSymmetricContainer (ℓ : Level) where

open import GpdCont.TwoCategory.Base using (TwoCategory)
open import GpdCont.TwoCategory.StrictFunctor using (StrictFunctor ; compStrictFunctor)
open import GpdCont.TwoCategory.StrictFunctor.LocalFunctor
  using (LocalFunctor ; isLocallyFullyFaithful ; isLocallyEssentiallySurjective)
open import GpdCont.TwoCategory.CompositeFunctor using (isLocallyFullyFaithfulCompositeRestrict)
open import GpdCont.GroupAction.Delooping using (isConnectedDeloopingBase)
open import GpdCont.ActionContainer.AsFamily ℓ
  using (Fam𝔹 ; isLocallyFullyFaithfulFam𝔹)
  renaming (FamAction to ActCont)

open import GpdCont.SetBundle.Base ℓ using () renaming (SetBundle to SymmCont)
open import GpdCont.SetBundle.Summation ℓ using (SetBundleΣ ; isLocallyFullyFaithfulΣ-at-connBase)

ActToSymmCont : StrictFunctor ActCont SymmCont
ActToSymmCont = compStrictFunctor Fam𝔹 SetBundleΣ

isLocallyFullyFaithfulActToSymmCont : isLocallyFullyFaithful ActToSymmCont
isLocallyFullyFaithfulActToSymmCont =
  isLocallyFullyFaithfulCompositeRestrict Fam𝔹 SetBundleΣ isLocallyFullyFaithfulFam𝔹 Σ-ff-restrict
  where
    open import Cubical.Categories.Functor using (Functor)
    module Fam𝔹 = StrictFunctor Fam𝔹

    Σ-ff-restrict : ∀ F G → Functor.isFullyFaithful (LocalFunctor SetBundleΣ (Fam𝔹.₀ F) (Fam𝔹.₀ G))
    Σ-ff-restrict F G = isLocallyFullyFaithfulΣ-at-connBase (Fam𝔹.₀ F) (Fam𝔹.₀ G) λ j → isConnectedDeloopingBase ℓ (F .snd j)

private
  module ActCont = TwoCategory ActCont
  module SymmCont = TwoCategory SymmCont
  module ActToSymmCont = StrictFunctor ActToSymmCont

isLocallyEso : isLocallyEssentiallySurjective ActToSymmCont
isLocallyEso F G = goal where module _ (g : SymmCont.hom (ActToSymmCont.₀ F) (ActToSymmCont.₀ G)) where
  open import GpdCont.TwoCategory.LocalCategory using (LocalCategory)
  open import GpdCont.Delooping.Base using (𝔹)
  open import Cubical.Categories.Category.Base using (CatIso ; pathToIso)
  open import Cubical.HITs.PropositionalTruncation.Monad


  goal : ∃[ f ∈ ActCont.hom F G ] CatIso (LocalCategory _ (ActToSymmCont.₀ F) (ActToSymmCont.₀ G)) (ActToSymmCont.₁ f) g
  goal = do
    let f₀ = λ s → g .fst (s , 𝔹.⋆) .fst
    return ((f₀ , λ s → {! !} , (λ y → g .snd (s , 𝔹.⋆) {! !}) , {! !}) , {! !})
