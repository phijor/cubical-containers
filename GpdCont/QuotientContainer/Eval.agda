open import GpdCont.QuotientContainer.Base

module GpdCont.QuotientContainer.Eval {ℓ} (Q : QCont ℓ) where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma.Properties as Sigma using (map-snd)
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)

open BinaryRelation using (isEquivRel ; isTrans ; isSym)

private
  open module Q = QCont Q

LabelEquiv : (s : Shape) (X : Type ℓ) → (v w : Q.Label X s) → Type ℓ
LabelEquiv s X v w = Σ[ σ ∈ Symm s ] PathP (λ i → ua (σ .fst) i → X) v w

-- TODO: Get rid of mentions of _∼_

_∼*_ : ∀ {s} {X : Type ℓ} → (v w : Pos s → X) → Type ℓ
_∼*_ {s} {X} = LabelEquiv s X

opaque
  isTrans-∼* : ∀ {s} {X : Type ℓ} → isTrans (_∼*_ {s} {X})
  isTrans-∼* v w u (σ , σ-label) (τ , τ-label) .fst = σ · τ
  isTrans-∼* {s} {X} v w u (σ , σ-label) (τ , τ-label) .snd = ua→ λ (pos : Pos s) →
    v pos ≡⟨ ua→⁻ σ-label pos ⟩
    w (σ⁺ pos) ≡⟨ ua→⁻ τ-label (σ⁺ pos) ⟩
    u (τ⁺ (σ⁺ pos)) ∎ where
      σ⁺ : Pos s → Pos s
      σ⁺ = equivFun (σ .fst)

      τ⁺ : Pos s → Pos s
      τ⁺ = equivFun (τ .fst)

  -- isTrans-∼* {s} {X} v w u σ* τ* .snd = λ i → comp (λ j → comp-equiv-square j i → X) (system i) {!isTransSymm  !} where
  --   σ τ σ∙τ : Pos s ≃ Pos s
  --   σ = σ* .fst .fst
  --   τ = τ* .fst .fst
  --   σ∙τ = σ ∙ₑ τ
  --   comp-equiv-square : compSquareFiller (ua σ) (ua τ) (ua σ∙τ)
  --   comp-equiv-square = uaCompEquivSquare (σ* .fst .fst) (τ* .fst .fst)

  --   system : (i j : I) → Partial (i ∨ ~ i) (comp-equiv-square j i → X)
  --   system i j (i = i0) = λ s → {! !}
  --   system i j (i = i1) = {!ua-unglue (σ∙τ) !}

∼*→PosEquiv : ∀ {X} {s} {v w : Pos s → X} → v ∼* w → Pos s ≃ Pos s
∼*→PosEquiv ((σ , is-symm-σ) , _) = σ

∼*→∼ : ∀ {X} {s} {v w : Pos s → X} → v ∼* w → Symm s
∼*→∼ ((σ , is-symm-σ) , _) = σ , is-symm-σ

∼*→PathP* : ∀ {X} {s} {v w : Pos s → X} → (σ : v ∼* w) → PathP (λ i → ua (∼*→PosEquiv σ) i → X) v w
∼*→PathP* ((_ , _) , p) = p

record ⟦_⟧ᵗ (X : Type ℓ) : Type ℓ where
  constructor mk⟦_,_⟧ᵗ
  field
    shape : Shape
    label-class : (Pos shape → X) / LabelEquiv shape X

unquoteDecl ⟦_⟧ᵗ-Iso-Σ = declareRecordIsoΣ ⟦_⟧ᵗ-Iso-Σ (quote ⟦_⟧ᵗ)

instance
  ⟦_⟧-to-Σ : ∀ {X : Type ℓ} → RecordToΣ (⟦_⟧ᵗ X)
  ⟦_⟧-to-Σ = toΣ ⟦_⟧ᵗ-Iso-Σ

open ⟦_⟧ᵗ

⟦_⟧ᵗ-rec : ∀ {X : Type ℓ} {ℓ'} {A : Type ℓ'}
  → isSet A
  → (on-label : ∀ {s} → (label : Pos s → X) → A)
  → (well-defined : ∀ {s} → (l₀ l₁ : Pos s → X) → l₀ ∼* l₁ → on-label l₀ ≡ on-label l₁)
  → ⟦_⟧ᵗ X → A
⟦_⟧ᵗ-rec is-set-A on-label well-defined mk⟦ shape , label-class ⟧ᵗ = SQ.rec is-set-A on-label well-defined label-class

Label→⟦_⟧ᵗ : ∀ {X} {s : Shape} → (v : Pos s → X) → ⟦_⟧ᵗ X
Label→⟦_⟧ᵗ {s} v .shape = s
Label→⟦_⟧ᵗ {s} v .label-class = SQ.[ v ]

⟦_⟧ᵗ-elimProp : ∀ {X : Type ℓ} {ℓ'} {P : ⟦_⟧ᵗ X → Type ℓ'}
  → (∀ x → isProp (P x))
  → (on-label : ∀ {s} (label : Pos s → X) → P (Label→⟦_⟧ᵗ label))
  → ∀ x → P x
⟦_⟧ᵗ-elimProp {P} is-prop-P on-label mk⟦ s , label-class ⟧ᵗ =
  SQ.elimProp {P = λ l → P mk⟦ s , l ⟧ᵗ}
    (λ l → is-prop-P mk⟦ s , l ⟧ᵗ)
    on-label
    label-class

opaque
  isSet-⟦_⟧ᵗ : ∀ X → isSet (⟦_⟧ᵗ X)
  isSet-⟦_⟧ᵗ X = recordIsOfHLevel 2 $ isSetΣ is-set-shape λ s → SQ.squash/

⟦_⟧′ : Type ℓ → hSet ℓ
⟦_⟧′ X .fst = ⟦_⟧ᵗ X
⟦_⟧′ X .snd = isSet-⟦_⟧ᵗ X

⟦_⟧ : hSet ℓ → hSet ℓ
⟦_⟧ X = ⟦_⟧′ ⟨ X ⟩

LabelClassPath→⟦_⟧Path : ∀ {X : Type ℓ} {s} → {v w : Q.Label X s / _∼*_} → v ≡ w → mk⟦ s , v ⟧ᵗ ≡ mk⟦ s , w ⟧ᵗ
LabelClassPath→⟦_⟧Path {s} p i .shape = s
LabelClassPath→⟦_⟧Path p i .label-class = p i

LabelEquiv→⟦_⟧Path : ∀ {X : Type ℓ} {s} → (v w : Q.Label X s) → v ∼* w → Label→⟦ v ⟧ᵗ ≡ Label→⟦ w ⟧ᵗ
LabelEquiv→⟦_⟧Path {s} v w eq i .shape = s
LabelEquiv→⟦_⟧Path {s} v w eq i .label-class = SQ.eq/ v w eq i

⟦_⟧ᵗ-elim : ∀ {X : Type ℓ} {ℓ'} {P : ⟦_⟧ᵗ X → Type ℓ'}
  → (∀ x → isSet (P x))
  → (on-label : ∀ {s} (label : Pos s → X) → P (Label→⟦_⟧ᵗ label))
  → (well-defined : ∀ {s} → (l₀ l₁ : Pos s → X) → (r : l₀ ∼* l₁) → PathP (λ i → P (LabelEquiv→⟦_⟧Path l₀ l₁ r i)) (on-label l₀) (on-label l₁))
  → ∀ x → P x
⟦_⟧ᵗ-elim {P} is-set-P on-label well-defined mk⟦ s , label-class ⟧ᵗ =
  SQ.elim {P = λ l → P mk⟦ s , l ⟧ᵗ}
    (λ l → is-set-P mk⟦ s , l ⟧ᵗ)
    on-label
    well-defined
    label-class

opaque
  preComp→⟦_⟧Path : ∀ {X : hSet ℓ} {s} → (v : Q.Label ⟨ X ⟩ s) (σ : Symm s) → Label→⟦ v ∘ σ ⁺ ⟧ᵗ ≡ Label→⟦ v ⟧ᵗ
  preComp→⟦_⟧Path {X} v σ = LabelEquiv→⟦_⟧Path {X = ⟨ X ⟩} (v ∘ σ ⁺) v (σ , ua→ λ pos → refl)

private
  module on-labels {X Y : Type ℓ} (f : X → Y) where
    private
      variable
        s : Shape
        v w : Pos s → X
    well-defined : (v w : Pos s → X) → v ∼* w → Path ((Pos s → Y) / _∼*_) SQ.[ f ∘ v ] SQ.[ f ∘ w ]
    well-defined v w (σ , σ-label) = SQ.eq/ _ _ r where
      r : (f ∘ v) ∼* (f ∘ w)
      r .fst = σ
      r .snd i pos = f (σ-label i pos)

    map : (Pos s → X) / _∼*_ → (Pos s → Y) / _∼*_
    map = SQ.rec SQ.squash/ (SQ.[_] ∘ (f ∘_)) well-defined

⟦_⟧-map : ∀ {X Y : hSet ℓ} (f : ⟨ X ⟩ → ⟨ Y ⟩) → ⟨ ⟦_⟧ X ⟩ → ⟨ ⟦_⟧ Y ⟩
⟦_⟧-map f x .shape = x .shape
⟦_⟧-map f x .label-class = on-labels.map f (x .label-class)

opaque
  ⟦_⟧-map-id : ∀ (X : hSet ℓ) → ⟦_⟧-map {X = X} {Y = X} (id ⟨ X ⟩) ≡ id ⟨ ⟦_⟧ X ⟩
  ⟦_⟧-map-id X = funExt $ λ x → LabelClassPath→⟦_⟧Path (on-labels-id (x .label-class)) where
    on-labels-id : ∀ {s} (label : (Pos s → ⟨ X ⟩) / _∼*_) → on-labels.map (id ⟨ X ⟩) label ≡ label
    on-labels-id = SQ.elimProp (λ label → SQ.squash/ (on-labels.map (id _) label) label) λ _ → refl

  ⟦_⟧-map-comp : ∀ {X Y Z : hSet ℓ} → (f : ⟨ X ⟩ → ⟨ Y ⟩) (g : ⟨ Y ⟩ → ⟨ Z ⟩)
    → ⟦_⟧-map {X} {Z} (g ∘ f) ≡ ⟦_⟧-map {Y} {Z} g ∘ ⟦_⟧-map {X} {Y} f
  ⟦_⟧-map-comp {X} f g = funExt $ λ x → LabelClassPath→⟦_⟧Path $ on-labels-comp _ (x .label-class) where
    on-labels-comp : ∀ s (label : (Pos s → ⟨ X ⟩) / _∼*_) → on-labels.map (g ∘ f) label ≡ on-labels.map g (on-labels.map f label)
    on-labels-comp s = SQ.elimProp (λ label → SQ.squash/ _ _) λ _ → refl
