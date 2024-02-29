open import GpdCont.Prelude
open import GpdCont.Coffin.Base

module GpdCont.Coffin.Lower {ℓ} (C : Coffin ℓ) where
  open import GpdCont.QuotientContainer.Base
  import GpdCont.Image

  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Univalence
  open import Cubical.Displayed.Base using (UARel)
  open import Cubical.Displayed.Generic using () renaming (𝒮-generic to PathUARel)

  open module C = Coffin C using (Shape ; Index ; Component)

  ↓Shape : Type ℓ
  ↓Shape = Index

  isSet-↓Shape : isSet ↓Shape
  isSet-↓Shape = C.is-set-index

  ↓PosSet : ↓Shape → hSet ℓ
  ↓PosSet = C.PosSet-pt

  ↓Pos : ↓Shape → Type ℓ
  ↓Pos = ⟨_⟩ ∘ ↓PosSet

  isSet-↓Pos : (s : ↓Shape) → isSet (↓Pos s)
  isSet-↓Pos = str ∘ ↓PosSet

  ↓PosCongEquiv : ∀ s t → UARel (↓Pos s ≃ ↓Pos t) ℓ
  ↓PosCongEquiv s t = PathUARel (↓Pos s ≃ ↓Pos t)

  open module ↓PosCongEquiv s t = UARel (↓PosCongEquiv s t)
    public
    using ()
    renaming (_≅_ to Pos[_≃_])

  module ↓PosCong {s t : ↓Shape} = GpdCont.Image (↓PosCongEquiv s t) (pathToEquiv ∘ cong ↓Pos)

  ↓Symm′ : ∀ {s t} → ↓Pos s ≃ ↓Pos t → hProp ℓ
  ↓Symm′ σ .fst = ↓PosCong.isInImage σ
  ↓Symm′ σ .snd = ↓PosCong.isPropIsInImage σ

  ↓Symm : ∀ {s t} → ↓Pos s ≃ ↓Pos t → Type ℓ
  ↓Symm {s} {t} = ⟨_⟩ ∘ ↓Symm′ {s} {t}

  isProp-↓Symm : ∀ {s t} → (σ : ↓Pos s ≃ ↓Pos t) → isProp (↓Symm σ)
  isProp-↓Symm {s} {t} = str ∘ ↓Symm′ {s} {t}
  
  ↓ : QCont ℓ
  ↓ .QCont.Shape = ↓Shape
  ↓ .QCont.Pos = ↓Pos
  ↓ .QCont.Symm = ↓Symm
  ↓ .QCont.is-set-shape = isSet-↓Shape
  ↓ .QCont.is-set-pos = isSet-↓Pos
  ↓ .QCont.is-prop-symm = isProp-↓Symm
  ↓ .QCont.symm-id = {! !}
  ↓ .QCont.symm-sym = {! !}
  ↓ .QCont.symm-comp = {! !}
