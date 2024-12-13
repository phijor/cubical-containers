open import GpdCont.Prelude

module GpdCont.ActionContainer.AsSymmetricContainer (ℓ : Level) where

open import GpdCont.TwoCategory.LaxFunctor using (LaxFunctor ; compLaxFunctor)
open import GpdCont.TwoCategory.LocalFunctor using (LocalFunctor ; isLocallyFullyFaithful)
open import GpdCont.TwoCategory.CompositeFunctor using (isLocallyFullyFaithfulCompositeRestrict)
open import GpdCont.GroupAction.Delooping using (isConnectedDeloopingBase)
open import GpdCont.ActionContainer.AsFamily ℓ
  using (Fam𝔹 ; isLocallyFullyFaithfulFam𝔹)
  renaming (FamAction to ActCont)

open import GpdCont.SetBundle.Base ℓ using () renaming (SetBundle to SymmCont)
open import GpdCont.SetBundle.Summation ℓ using (SetBundleΣ ; isLocallyFullyFaithfulΣ-at-connBase)

ActToSymmCont : LaxFunctor ActCont SymmCont
ActToSymmCont = compLaxFunctor Fam𝔹 SetBundleΣ

isLocallyFullyFaithfulActToSymmCont : isLocallyFullyFaithful ActToSymmCont
isLocallyFullyFaithfulActToSymmCont =
  isLocallyFullyFaithfulCompositeRestrict Fam𝔹 SetBundleΣ isLocallyFullyFaithfulFam𝔹 Σ-ff-restrict
  where
    open import Cubical.Categories.Functor using (Functor)
    module Fam𝔹 = LaxFunctor Fam𝔹

    Σ-ff-restrict : ∀ F G → Functor.isFullyFaithful (LocalFunctor SetBundleΣ (Fam𝔹.₀ F) (Fam𝔹.₀ G))
    Σ-ff-restrict F G = isLocallyFullyFaithfulΣ-at-connBase (Fam𝔹.₀ F) (Fam𝔹.₀ G) λ j → isConnectedDeloopingBase ℓ (F .snd j)
