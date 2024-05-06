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

⟦_⟧ᵗ : Type ℓ → Type ℓ
⟦_⟧ᵗ X = Σ[ s ∈ Shape ] (Pos s → X) / _∼*_

opaque
  mk⟦_⟧ᵗ : ∀ {X} → Σ[ s ∈ Shape ] ((Pos s → X) / _∼*_) → ⟦_⟧ᵗ X
  mk⟦_⟧ᵗ x = x

  Label→⟦_⟧ᵗ : ∀ {X} {s : Shape} → (v : Pos s → X) → ⟦_⟧ᵗ X
  Label→⟦_⟧ᵗ {s} v = (s , SQ.[ v ])

  isSet-⟦_⟧ᵗ : ∀ X → isSet (⟦_⟧ᵗ X)
  isSet-⟦_⟧ᵗ X = isSetΣ is-set-shape λ s → SQ.squash/

  ⟦_⟧′ : Type ℓ → hSet ℓ
  ⟦_⟧′ X .fst = ⟦_⟧ᵗ X
  ⟦_⟧′ X .snd = isSet-⟦_⟧ᵗ X

  ⟦_⟧ : hSet ℓ → hSet ℓ
  ⟦_⟧ X = ⟦_⟧′ ⟨ X ⟩

LabelEquiv→⟦_⟧Path : ∀ {X : hSet ℓ} {s} → (v w : Q.Label ⟨ X ⟩ s) → v ∼* w → Path (⟦_⟧ᵗ ⟨ X ⟩) (s , SQ.[ v ]) (s , SQ.[ w ])
LabelEquiv→⟦_⟧Path {s} v w eq i .fst = s
LabelEquiv→⟦_⟧Path {s} v w eq i .snd = SQ.eq/ v w eq i

opaque
  preComp→⟦_⟧Path : ∀ {X : hSet ℓ} {s} → (v : Q.Label ⟨ X ⟩ s) (σ : Symm s) → Path (⟦_⟧ᵗ ⟨ X ⟩) (s , SQ.[ v ∘ σ ⁺ ]) (s , SQ.[ v ])
  preComp→⟦_⟧Path {X} v σ = LabelEquiv→⟦_⟧Path {X = X} (v ∘ σ ⁺) v (σ , ua→ λ pos → refl)

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

opaque
  unfolding ⟦_⟧
  ⟦_⟧-map : ∀ {X Y : hSet ℓ} (f : ⟨ X ⟩ → ⟨ Y ⟩) → ⟨ ⟦_⟧ X ⟩ → ⟨ ⟦_⟧ Y ⟩
  ⟦_⟧-map {X} {Y} f = map-snd (on-labels.map f)

  ⟦_⟧-map-id : ∀ (X : hSet ℓ) → ⟦_⟧-map (id ⟨ X ⟩) ≡ id ⟨ ⟦_⟧ X ⟩
  ⟦_⟧-map-id X = funExt $ uncurry λ s label → Sigma.ΣPathP (refl {x = s} , on-labels-id s label) where
    on-labels-id : ∀ s (label : (Pos s → ⟨ X ⟩) / _∼*_) → on-labels.map (id ⟨ X ⟩) label ≡ label
    on-labels-id s = SQ.elimProp (λ label → SQ.squash/ (on-labels.map (id _) label) label) λ _ → refl

  ⟦_⟧-map-comp : ∀ {X Y Z : hSet ℓ} → (f : ⟨ X ⟩ → ⟨ Y ⟩) (g : ⟨ Y ⟩ → ⟨ Z ⟩)
    → ⟦_⟧-map {X} {Z} (g ∘ f) ≡ ⟦_⟧-map {Y} {Z} g ∘ ⟦_⟧-map f
  ⟦_⟧-map-comp {X} f g = funExt $ uncurry λ s label → Sigma.ΣPathP (refl , on-labels-comp s label) where
    on-labels-comp : ∀ s (label : (Pos s → ⟨ X ⟩) / _∼*_) → on-labels.map (g ∘ f) label ≡ on-labels.map g (on-labels.map f label)
    on-labels-comp s = SQ.elimProp (λ label → SQ.squash/ _ _) λ _ → refl
