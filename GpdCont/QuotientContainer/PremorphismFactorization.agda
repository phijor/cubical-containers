{-# OPTIONS --lossy-unification #-}
module GpdCont.QuotientContainer.PremorphismFactorization where

open import GpdCont.Prelude
open import GpdCont.QuotientContainer.Base
open import GpdCont.QuotientContainer.Premorphism
open import GpdCont.Univalence using (→ua ; ua→)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (isEquivInvEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport using (funTypeTransp)
open import Cubical.Foundations.Univalence hiding (ua→)
open import Cubical.Data.Sigma
open import Cubical.Functions.Image
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv
open import Cubical.HITs.PropositionalTruncation as PT using ()

private
  ImageOf : ∀ {ℓA ℓB} ℓ {A : Type ℓA} {B : Type ℓB} → (f : A → B) → Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-suc ℓ))
  ImageOf ℓ {A} {B} f = Σ[ Im ∈ Type ℓ ] Σ[ e ∈ (A ↠ Im) ] Σ[ m ∈ (Im ↪ B) ] m .fst ∘ e .fst ≡ f

  isPropImageOf : ∀ {ℓ ℓA ℓB} {A : Type ℓA} {B : Type ℓB} (f : A → B) → isProp (ImageOf ℓ f)
  isPropImageOf {A} {B} f (Im₀ , e₀ , m₀ , p₀) (Im₁ , e₁ , m₁ , p₁) = ΣPathP (Im-path , ΣPathP (e-path , ΣPathP (m-path , p-path))) where
    p : m₀ .fst ∘ e₀ .fst ≡ m₁ .fst ∘ e₁ .fst
    p = p₀ ∙ sym p₁

    ι : Im₀ ≃ Im₁
    ι = imagesEquiv e₀ m₀ e₁ m₁ p

    Im-path : Im₀ ≡ Im₁
    Im-path = ua ι

    e-comm : (a : A) → equivFun ι (e₀ .fst a) ≡ (e₁ .fst a)
    e-comm = imagesSurjectionComm e₀ m₀ e₁ m₁ p

    e-path' : PathP (λ i → A → Im-path i) (e₀ .fst) (e₁ .fst)
    e-path' = →ua e-comm

    e-path : PathP (λ i → A ↠ Im-path i) e₀ e₁
    e-path i .fst = e-path' i
    e-path i .snd = isProp→PathP {B = λ i → isSurjection (e-path i .fst)} (λ _ → isPropIsSurjection) (e₀ .snd) (e₁ .snd) i

    m-comm : (im₀ : Im₀) → m₀ .fst im₀ ≡ m₁ .fst (equivFun ι $ im₀)
    m-comm = sym ∘ imagesEmbeddingComm e₀ m₀ e₁ m₁ p

    m-path' : PathP (λ i → Im-path i → B) (m₀ .fst) (m₁ .fst)
    m-path' = ua→ m-comm

    m-path : PathP (λ i → Im-path i ↪ B) m₀ m₁
    m-path i .fst = m-path' i
    m-path i .snd = isProp→PathP {B = λ i → isEmbedding (m-path i .fst)} (λ _ → isPropIsEmbedding) (m₀ .snd) (m₁ .snd) i

    p-path : PathP (λ i → (λ x → m-path' i (e-path' i x)) ≡ f) p₀ p₁
    p-path i j a = {! !}

  isContrImageOf : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} (f : A → B) → isContr (ImageOf (ℓ-max ℓA ℓB) f)
  isContrImageOf f = inhProp→isContr
    (Image f , (restrictToImage f , isSurjectionImageRestriction f) , imageInclusion f , imageFactorization f)
    (isPropImageOf f)

  opaque
    wedge : ∀ {ℓ} {A B C D : Type ℓ} (e : A ↠ B) (f g : B → C) (m : C ↪ D)
      → (m .fst) ∘ f ∘ (e .fst) ≡ (m .fst) ∘ g ∘ (e .fst)
      → f ≡ g
    wedge e f g m p = step₂ where
      step₁ : f ∘ (e .fst) ≡ g ∘ (e .fst)
      step₁ = funExt λ a → isEmbedding→Inj (m .snd) _ _ (funExt⁻ p a)

      step₂ : f ≡ g
      step₂ = funExt λ b → {! !}


open QCont
open Premorphism

module _ {ℓ} (Q R : QCont ℓ) (u : Q .QCont.Shape → R .QCont.Shape) (α : Premorphism Q R u) where
  private
    module Q = QCont Q
    module R = QCont R

    open Premorphism α renaming (pos-mor to f ; symm-pres to Φ ; symm-pres-natural to Φ-nat)

  PosImageEquiv : ∀ (s : Q.Shape) (g : Q.Symm s) → Image (f s) ≃ Image (f s)
  PosImageEquiv s g = imagesEquiv f-res f-inc f*Φ-res f*Φ-inc comm where
    f-res : R.Pos (u s) ↠ Image (f s)
    f-res .fst = restrictToImage _
    f-res .snd = isSurjectionImageRestriction _

    f-inc = imageInclusion (f s)

    Φg⁺ : R.Pos (u s) → R.Pos (u s)
    Φg⁺ = Φ s g R.⁺

    Φg : R.Pos (u s) ↠ R.Pos (u s)
    Φg .fst = Φg⁺
    Φg .snd = isEquiv→isSurjection (Φ s g .fst .snd)

    f*Φ-res : R.Pos (u s) ↠ Image (f s)
    f*Φ-res = compSurjection Φg f-res

    g⁺ : Q .Pos s → Q .Pos s
    g⁺ = g Q.⁺

    g⁻ : Q .Pos s → Q .Pos s
    g⁻ = g Q.⁻

    g-emb : Q.Pos s ↪ Q.Pos s
    g-emb = Equiv→Embedding (invEquiv (g .fst))

    f*Φ-inc : Image (f s) ↪ Q.Pos s
    f*Φ-inc = compEmbedding g-emb f-inc

    comm : imageInclusion (f s) .fst ∘ restrictToImage (f s) ≡ f*Φ-inc .fst ∘ f*Φ-res .fst
    comm =
      imageInclusion (f s) .fst ∘ restrictToImage (f s) ≡⟨ imageFactorization $ f s ⟩
      f s ≡⟨ cong (λ - → - ∘ f s) (sym $ funExt (retEq $ g .fst)) ⟩
      g⁻ ∘ g⁺ ∘ f s ≡⟨ cong (g⁻ ∘_) (Φ-nat s g) ⟩
      g⁻ ∘ f s ∘ Φg .fst ≡⟨ cong (λ - → g⁻ ∘ - ∘ Φg⁺) $ sym (imageFactorization $ f s) ⟩
      g⁻ ∘ imageInclusion (f s) .fst ∘ restrictToImage (f s) ∘ Φg⁺ ≡⟨⟩
      f*Φ-inc .fst ∘ f*Φ-res .fst ∎

  opaque
    PosImageEquivFunctorial : ∀ {s} (g h : Q.Symm s) → PosImageEquiv s (g Q.· h) ≡ PosImageEquiv s g ∙ₑ PosImageEquiv s h
    PosImageEquivFunctorial {s} g h = {!isContrImageOf (f s) .snd  !} where
      ImComp : ImageOf _ (f s)
      ImComp .fst = Image (f s)
      ImComp .snd .fst = {! !}
      ImComp .snd .snd = {! !}

  ImageSymm : ∀ {s} → Image (f s) ≃ Image (f s) → Type ℓ
  ImageSymm {s} = isInImage (PosImageEquiv s)

  opaque
    compImageSymm : ∀ {s} (k k′ : Image (f s) ≃ Image (f s)) → ImageSymm k → ImageSymm k′ → ImageSymm (k ∙ₑ k′)
    compImageSymm {s} k k′ = PT.map2 λ (g , p) (g′ , p′) → lem g g′ p p′ where
      lem : (g g′ : Q.Symm s) → PosImageEquiv s g ≡ k → PosImageEquiv s g′ ≡ k′ → Σ[ h ∈ Q.Symm s ] PosImageEquiv s h ≡ k ∙ₑ k′
      lem g g′ f*g≡k f*g′≡k′ .fst = g Q.· g′
      lem g g′ f*g≡k f*g′≡k′ .snd =
        PosImageEquiv s (g Q.· g′) ≡⟨ PosImageEquivFunctorial g g′ ⟩
        PosImageEquiv s g ∙ₑ PosImageEquiv s g′ ≡⟨ cong₂ _∙ₑ_ f*g≡k f*g′≡k′ ⟩
        k ∙ₑ k′ ∎

  ImCont : QCont ℓ
  ImCont .Shape = Q.Shape
  ImCont .Pos s = Image (f s)
  ImCont .isSymm = ImageSymm
  ImCont .is-set-shape = Q.is-set-shape
  ImCont .is-set-pos s = isSetΣSndProp (Q.is-set-pos s) (isPropIsInImage _)
  ImCont .is-prop-symm = isPropIsInImage (PosImageEquiv _)
  ImCont .symm-id = {! !}
  ImCont .symm-sym = {! !}
  ImCont .symm-comp = compImageSymm
