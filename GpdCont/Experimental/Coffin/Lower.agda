open import GpdCont.Prelude
open import GpdCont.Experimental.Coffin.Base

module GpdCont.Experimental.Coffin.Lower {ℓ} (C : Coffin ℓ) where
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

  ↓isSymm : ∀ {s} → ↓Pos s ≃ ↓Pos s → Type ℓ
  ↓isSymm = isInImage (pathToEquiv ∘ cong Pos)

  private
    ↓isSymm∞ : ∀ {s} → ↓Pos s ≃ ↓Pos s → Type ℓ
    ↓isSymm∞ {s} σ = Σ[ p ∈ sk s ≡ sk s  ] pathToEquiv (cong Pos p) ≡ σ

    _ : ∀ {s} → (σ : ↓Pos s ≃ ↓Pos s) → ↓isSymm σ ≡ ∥ ↓isSymm∞ σ ∥₁
    _ = λ σ → refl

  isProp-↓isSymm : ∀ {s} → (σ : ↓Pos s ≃ ↓Pos s) → isProp (↓isSymm σ)
  isProp-↓isSymm σ = PT.isPropPropTrunc

  ↓isSymm-id : ∀ s → ↓isSymm (idEquiv $ ↓Pos s)
  ↓isSymm-id s = PT.∣ refl , pathToEquivRefl ∣₁

  ↓isSymm-sym : ∀ {s} → (σ : ↓Pos s ≃ ↓Pos s) → ↓isSymm σ → ↓isSymm (invEquiv σ)
  ↓isSymm-sym {s} σ = PT.map $ uncurry symm-σ⁻¹ where
    module _ (p : sk s ≡ sk s) (im-p≡σ : pathToEquiv (cong Pos p) ≡ σ) where
      sk-path : sk s ≡ sk s
      sk-path = sym p

      opaque
        cong-Pos-path : pathToEquiv (cong Pos sk-path) ≡ invEquiv σ
        cong-Pos-path = pathToEquivSym (cong Pos p) ∙ cong invEquiv im-p≡σ

      symm-σ⁻¹ : ↓isSymm∞ (invEquiv σ)
      symm-σ⁻¹ .fst = sk-path
      symm-σ⁻¹ .snd = cong-Pos-path

  ↓isSymm-comp : ∀ {s} (σ : ↓Pos s ≃ ↓Pos s) (τ : ↓Pos s ≃ ↓Pos s)
    → ↓isSymm σ → ↓isSymm τ
    → ↓isSymm (σ ∙ₑ τ)
  ↓isSymm-comp σ τ = PT.map2 symm-∙ where
    module _ ((p , im-p≡σ) : ↓isSymm∞ σ) ((q , im-q≡τ) : ↓isSymm∞ τ) where
      opaque
        im-p∙q≡σ∙τ : pathToEquiv (cong Pos (p ∙ q)) ≡ σ ∙ₑ τ
        im-p∙q≡σ∙τ =
          pathToEquiv (cong Pos (p ∙ q))        ≡⟨ cong pathToEquiv (congFunct Pos p q) ⟩
          pathToEquiv (cong Pos p ∙ cong Pos q) ≡⟨ pathToEquivComp _ _ ⟩
          pathToEquiv (cong Pos p) ∙ₑ pathToEquiv (cong Pos q) ≡⟨ cong₂ _∙ₑ_ im-p≡σ im-q≡τ ⟩
          σ ∙ₑ τ ∎

      symm-∙ : ↓isSymm∞ (σ ∙ₑ τ)
      symm-∙ .fst = p ∙ q
      symm-∙ .snd = im-p∙q≡σ∙τ

  ↓ : QCont ℓ
  ↓ .QCont.Shape = ↓Shape
  ↓ .QCont.Pos = ↓Pos
  ↓ .QCont.isSymm = ↓isSymm
  ↓ .QCont.is-set-shape = isSet-↓Shape
  ↓ .QCont.is-set-pos = isSet-↓Pos
  ↓ .QCont.is-prop-symm = isProp-↓isSymm
  ↓ .QCont.symm-id = ↓isSymm-id
  ↓ .QCont.symm-sym = ↓isSymm-sym
  ↓ .QCont.symm-comp = ↓isSymm-comp
