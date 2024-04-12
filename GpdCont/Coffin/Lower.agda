open import GpdCont.Prelude
open import GpdCont.Coffin.Base

module GpdCont.Coffin.Lower {ℓ} (C : Coffin ℓ) where
  open import GpdCont.QuotientContainer.Base
  open import GpdCont.Equiv using (pathToEquivSym ; pathToEquivComp)

  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Univalence
  open import Cubical.Foundations.GroupoidLaws using (congFunct)
  open import Cubical.Functions.Image using (isInImage)
  open import Cubical.Data.Sigma.Base
  open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

  private
    open module C = Coffin C using (Shape ; Pos ; Index ; Component)

  ↓Shape : Type ℓ
  ↓Shape = Index

  isSet-↓Shape : isSet ↓Shape
  isSet-↓Shape = C.isSetIndex

  private
    sk : ↓Shape → Shape
    sk = C.sk

  ↓PosSet : ↓Shape → hSet ℓ
  ↓PosSet ix = C.PosSet (sk ix)

  ↓Pos : ↓Shape → Type ℓ
  ↓Pos = ⟨_⟩ ∘ ↓PosSet

  isSet-↓Pos : (s : ↓Shape) → isSet (↓Pos s)
  isSet-↓Pos = str ∘ ↓PosSet

  ↓Symm : ∀ {s t} → ↓Pos s ≃ ↓Pos t → Type ℓ
  ↓Symm = isInImage (pathToEquiv ∘ cong Pos)

  private
    ↓Symm∞ : ∀ {s t} → ↓Pos s ≃ ↓Pos t → Type ℓ
    ↓Symm∞ {s} {t} σ = Σ[ p ∈ sk s ≡ sk t  ] pathToEquiv (cong Pos p) ≡ σ

    _ : ∀ {s t} → (σ : ↓Pos s ≃ ↓Pos t) → ↓Symm σ ≡ ∥ ↓Symm∞ σ ∥₁
    _ = λ σ → refl

  isProp-↓Symm : ∀ {s t} → (σ : ↓Pos s ≃ ↓Pos t) → isProp (↓Symm σ)
  isProp-↓Symm σ = PT.isPropPropTrunc

  ↓Symm-id : ∀ s → ↓Symm (idEquiv $ ↓Pos s)
  ↓Symm-id s = PT.∣ refl , pathToEquivRefl ∣₁

  ↓Symm-sym : ∀ {s t} → (σ : ↓Pos s ≃ ↓Pos t) → ↓Symm σ → ↓Symm (invEquiv σ)
  ↓Symm-sym {s} {t} σ = PT.map $ uncurry symm-σ⁻¹ where
    module _ (p : sk s ≡ sk t) (im-p≡σ : pathToEquiv (cong Pos p) ≡ σ) where
      sk-path : sk t ≡ sk s
      sk-path = sym p

      opaque
        cong-Pos-path : pathToEquiv (cong Pos sk-path) ≡ invEquiv σ
        cong-Pos-path = pathToEquivSym (cong Pos p) ∙ cong invEquiv im-p≡σ

      symm-σ⁻¹ : ↓Symm∞ (invEquiv σ)
      symm-σ⁻¹ .fst = sk-path
      symm-σ⁻¹ .snd = cong-Pos-path

  ↓Symm-comp : ∀ {s t u} (σ : ↓Pos s ≃ ↓Pos t) (τ : ↓Pos t ≃ ↓Pos u)
    → ↓Symm σ → ↓Symm τ
    → ↓Symm (σ ∙ₑ τ)
  ↓Symm-comp σ τ = PT.map2 symm-∙ where
    module _ ((p , im-p≡σ) : ↓Symm∞ σ) ((q , im-q≡τ) : ↓Symm∞ τ) where
      opaque
        im-p∙q≡σ∙τ : pathToEquiv (cong Pos (p ∙ q)) ≡ σ ∙ₑ τ
        im-p∙q≡σ∙τ =
          pathToEquiv (cong Pos (p ∙ q))        ≡⟨ cong pathToEquiv (congFunct Pos p q) ⟩
          pathToEquiv (cong Pos p ∙ cong Pos q) ≡⟨ pathToEquivComp _ _ ⟩
          pathToEquiv (cong Pos p) ∙ₑ pathToEquiv (cong Pos q) ≡⟨ cong₂ _∙ₑ_ im-p≡σ im-q≡τ ⟩
          σ ∙ₑ τ ∎

      symm-∙ : ↓Symm∞ (σ ∙ₑ τ)
      symm-∙ .fst = p ∙ q
      symm-∙ .snd = im-p∙q≡σ∙τ

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
