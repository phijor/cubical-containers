module GpdCont.QuotientContainer.Morphism where

open import GpdCont.Prelude
open import GpdCont.QuotientContainer.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level
    Q R S : QCont ℓ

record QContMorphism {ℓ} (Q R : QCont ℓ) : Type ℓ where
  private
    module Q = QCont Q
    module R = QCont R

  field
    shape-mor : Q.Shape → R.Shape
    pos-equiv : ∀ (s : Q.Shape) → R.Pos (shape-mor s) ≃ Q.Pos s

  field
    symm-pres : ∀ (s : Q.Shape) → s Q.∼ s → shape-mor s R.∼ shape-mor s
    symm-pres-natural : ∀ (s : Q.Shape) (σ : s Q.∼ s)
      → pos-equiv s ∙ₑ (σ .fst) ≡ (symm-pres s σ .fst) ∙ₑ (pos-equiv s)

    -- The morphism of shapes preserves the subgroup of symmetries, naturally:
    --
    --                           pos-equiv s
    --      R.Pos (shape-mor s) ------------> Q.Pos s
    --               |                           |
    --               |                           |
    -- symm-pres s σ |                           | σ
    --               |                           |
    --               v                           v
    --      R.Pos (shape-mor s) ------------> Q.Pos s
    --                           pos-equiv s

  private
    conj : ∀ {s : Q.Shape} (σ : Q.PosΩ s) → R.PosΩ (shape-mor s)
    conj {s} σ = pos-equiv s ∙ₑ σ ∙ₑ invEquiv (pos-equiv s)

unquoteDecl QContMorphismIsoΣ = declareRecordIsoΣ QContMorphismIsoΣ (quote QContMorphism)

instance
  QContMorphismToΣ : ∀ {ℓ} {Q R : QCont ℓ} → RecordToΣ (QContMorphism Q R)
  QContMorphismToΣ = toΣ QContMorphismIsoΣ

isSetQContMorphism : isSet (QContMorphism Q R)
isSetQContMorphism {Q} {R} =
  recordIsOfHLevel 2 $ isSetΣ isSet-shape-mor
    λ shape-mor → isSetΣ (isSet-pos-equiv shape-mor)
    λ pos-equiv → isSetΣ (isSet-symm-pres shape-mor)
    λ symm-pres → isProp→isSet (isProp-symm-pres-natural shape-mor pos-equiv symm-pres) where
  private
    module Q = QCont Q
    module R = QCont R
  
  isSet-shape-mor : isSet (Q.Shape → R.Shape)
  isSet-shape-mor = isSet→ (QCont.is-set-shape R)

  isSet-pos-equiv : ∀ shape-mor → isSet (∀ s → R.Pos (shape-mor s) ≃ Q.Pos s)
  isSet-pos-equiv _ = isSetΠ λ _ → isOfHLevel≃ 2 (QCont.is-set-pos R _) (QCont.is-set-pos Q _)

  isSet-symm-pres : ∀ (shape-mor : Q.Shape → _) → isSet (∀ s → s Q.∼ s → shape-mor s R.∼ shape-mor s)
  isSet-symm-pres _ = isSetΠ2 λ s σ → R.isSet-∼

  isProp-symm-pres-natural : ∀ shape-mor (pos-equiv : ∀ s → R.Pos (shape-mor s) ≃ Q.Pos s) symm-pres → isProp (∀ s σ → pos-equiv s ∙ₑ σ .fst ≡ symm-pres s σ .fst ∙ₑ pos-equiv s)
  isProp-symm-pres-natural _ _ _ = isPropΠ2 λ _ _ → isOfHLevel≃ 2 (R.is-set-pos _) (Q.is-set-pos _) _ _

module _ (α β : QContMorphism Q R) where
  private
    module α = QContMorphism α
    module β = QContMorphism β

  path-lemma : (p : α.shape-mor ≡ β.shape-mor)
    → {! !}
    → α ≡ β
  path-lemma = {! !}

QContId : (Q : QCont ℓ) → QContMorphism Q Q
QContId Q .QContMorphism.shape-mor = id $ Q .QCont.Shape
QContId Q .QContMorphism.pos-equiv = idEquiv ∘ Q .QCont.Pos
QContId Q .QContMorphism.symm-pres s = id (QCont._∼_ Q s s)
QContId Q .QContMorphism.symm-pres-natural s σ = equivEq refl

compQContMorphism : (α : QContMorphism Q R) (β : QContMorphism R S) → QContMorphism Q S
compQContMorphism {Q} {R} {S} α β = composite where
  module α = QContMorphism α
  module β = QContMorphism β
  module S = QCont S

  composite : QContMorphism Q S
  composite .QContMorphism.shape-mor = β.shape-mor ∘ α.shape-mor
  composite .QContMorphism.pos-equiv s = β.pos-equiv (α.shape-mor s) ∙ₑ α.pos-equiv s
  composite .QContMorphism.symm-pres s σ = β.symm-pres (α.shape-mor s) (α.symm-pres s σ)
  composite .QContMorphism.symm-pres-natural s σ =
    (β.pos-equiv (α.shape-mor s) ∙ₑ α.pos-equiv s) ∙ₑ σ .fst
      ≡⟨ sym (compEquiv-assoc _ _ _) ⟩
    β.pos-equiv (α.shape-mor s) ∙ₑ (α.pos-equiv s ∙ₑ σ .fst)
      ≡⟨ cong (β.pos-equiv _ ∙ₑ_) (α.symm-pres-natural s σ) ⟩
    β.pos-equiv (α.shape-mor s) ∙ₑ (α.symm-pres s σ .fst ∙ₑ α.pos-equiv s)
      ≡⟨ compEquiv-assoc _ _ _ ⟩
    (β.pos-equiv (α.shape-mor s) ∙ₑ α.symm-pres s σ .fst) ∙ₑ α.pos-equiv s
      ≡⟨ cong (_∙ₑ α.pos-equiv s) (β.symm-pres-natural (α.shape-mor s) (α.symm-pres s σ)) ⟩
    (β.symm-pres (α.shape-mor s) (α.symm-pres s σ) .fst ∙ₑ β.pos-equiv (α.shape-mor s)) ∙ₑ α.pos-equiv s
      ≡⟨ sym (compEquiv-assoc _ _ _) ⟩
    β.symm-pres (α.shape-mor s) (α.symm-pres s σ) .fst ∙ₑ (β.pos-equiv (α.shape-mor s) ∙ₑ α.pos-equiv s)
      ∎
