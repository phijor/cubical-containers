open import GpdCont.Prelude

open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.StrictFunctor

module GpdCont.TwoCategory.CompositeFunctor
  {ℓo₁ ℓh₁ ℓr₁}
  {ℓo₂ ℓh₂ ℓr₂}
  {ℓo₃ ℓh₃ ℓr₃}
  {C : TwoCategory ℓo₁ ℓh₁ ℓr₁}
  {D : TwoCategory ℓo₂ ℓh₂ ℓr₂}
  {E : TwoCategory ℓo₃ ℓh₃ ℓr₃}
  (F : StrictFunctor C D)
  (G : StrictFunctor D E)
  where
  private
    module C = TwoCategory C
    module F = StrictFunctor F

  open import GpdCont.TwoCategory.StrictFunctor.LocalFunctor
  open import Cubical.Categories.Functor.Base using (Functor)
  open import Cubical.Categories.Functor.Properties using (isFullyFaithfulG∘F)

  isLocallyFullyFaithfulCompositeRestrict :
      isLocallyFullyFaithful F
    → (∀ (c₁ c₂ : C.ob) → Functor.isFullyFaithful (LocalFunctor G (F.₀ c₁) (F.₀ c₂)))
    → isLocallyFullyFaithful (compStrictFunctor F G)
  isLocallyFullyFaithfulCompositeRestrict F-ff G-ff c₁ c₂ = isFullyFaithfulG∘F
    {F = LocalFunctor F c₁ c₂}
    {G = LocalFunctor G (F.₀ c₁) (F.₀ c₂)}
    (F-ff c₁ c₂)
    (G-ff c₁ c₂)
