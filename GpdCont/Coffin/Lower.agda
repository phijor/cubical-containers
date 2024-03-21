open import GpdCont.Prelude
open import GpdCont.Coffin.Base

module GpdCont.Coffin.Lower {ℓ} (C : Coffin ℓ) where
  open import GpdCont.QuotientContainer.Base
  open import GpdCont.Equiv using (pathToEquivSym ; pathToEquivComp)

  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Univalence
  open import Cubical.Foundations.GroupoidLaws using (congFunct)
  open import Cubical.Data.Sigma.Base
  import Cubical.HITs.PropositionalTruncation as PT

  open module C = Coffin C using (Shape ; Pos ; Index ; Component)

  ↓Shape : Type ℓ
  ↓Shape = Index

  isSet-↓Shape : isSet ↓Shape
  isSet-↓Shape = C.isSetIndex

  private
    sk : ↓Shape → Shape
    sk = C.sk

  ↓PosSet : ↓Shape → hSet ℓ
  ↓PosSet = C.PosSetIndex

  ↓Pos : ↓Shape → Type ℓ
  ↓Pos = ⟨_⟩ ∘ ↓PosSet

  isSet-↓Pos : (s : ↓Shape) → isSet (↓Pos s)
  isSet-↓Pos = str ∘ ↓PosSet

  -- TODO: This is wrong and should quantify over (p : sk s ≡ sk t)!!!
  ↓Symm : ∀ {s t} → ↓Pos s ≃ ↓Pos t → Type ℓ
  ↓Symm {s} {t} σ = ∃[ p ∈ s ≡ t  ] pathToEquiv (cong ↓Pos p) ≡ σ

  isProp-↓Symm : ∀ {s t} → (σ : ↓Pos s ≃ ↓Pos t) → isProp (↓Symm σ)
  isProp-↓Symm σ = PT.isPropPropTrunc

  ↓Symm-id : ∀ s → ↓Symm (idEquiv $ ↓Pos s)
  ↓Symm-id s = PT.∣ refl , pathToEquivRefl ∣₁

  ↓Symm-sym : ∀ {s t} → (σ : ↓Pos s ≃ ↓Pos t) → ↓Symm σ → ↓Symm (invEquiv σ)
  ↓Symm-sym σ = PT.map λ where
    (p , ↓Pos*[p]≡σ) → sym p , pathToEquivSym (cong ↓Pos p) ∙ cong invEquiv ↓Pos*[p]≡σ

  ↓Symm-comp : ∀ {s t u} (σ : ↓Pos s ≃ ↓Pos t) (τ : ↓Pos t ≃ ↓Pos u)
    → ↓Symm σ → ↓Symm τ
    → ↓Symm (σ ∙ₑ τ)
  ↓Symm-comp σ τ = PT.map2 λ where
    (p , im-p≡σ) (q , im-q≡τ) .fst → p ∙ q
    (p , im-p≡σ) (q , im-q≡τ) .snd →
      pathToEquiv (cong ↓Pos (p ∙ q)) ≡⟨ cong pathToEquiv (congFunct ↓Pos p q) ⟩
      pathToEquiv (cong ↓Pos p ∙ cong ↓Pos q) ≡⟨ pathToEquivComp _ _ ⟩
      pathToEquiv (cong ↓Pos p) ∙ₑ pathToEquiv (cong ↓Pos q) ≡⟨ cong₂ _∙ₑ_ im-p≡σ im-q≡τ ⟩
      σ ∙ₑ τ ∎

  ↓ : QCont ℓ
  ↓ .QCont.Shape = ↓Shape
  ↓ .QCont.Pos = ↓Pos
  ↓ .QCont.Symm = ↓Symm
  ↓ .QCont.is-set-shape = isSet-↓Shape
  ↓ .QCont.is-set-pos = isSet-↓Pos
  ↓ .QCont.is-prop-symm = isProp-↓Symm
  ↓ .QCont.symm-id = ↓Symm-id
  ↓ .QCont.symm-sym = ↓Symm-sym
  ↓ .QCont.symm-comp = ↓Symm-comp
