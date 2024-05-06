module GpdCont.QuotientContainer.Premorphism where

open import GpdCont.Prelude
open import GpdCont.QuotientContainer.Base

open import Cubical.Foundations.HLevels

record Premorphism {ℓ} (Q R : QCont ℓ) (shape-mor : Q .QCont.Shape → R .QCont.Shape) : Type ℓ where
  eta-equality
  private
    module Q = QCont Q
    module R = QCont R

  field
    pos-mor : ∀ (s : Q.Shape) → R.Pos (shape-mor s) → Q.Pos s

  field
    symm-pres : ∀ (s : Q.Shape) → Q.Symm s → R.Symm (shape-mor s)
    symm-pres-natural : ∀ (s : Q.Shape) (σ : Q.Symm s)
      → pos-mor s Q.▷ σ ≡ (symm-pres s σ) R.◁ (pos-mor s)

    -- The morphism of shapes preserves the subgroup of symmetries, naturally:
    --
    --                           pos-mor s
    --      R.Pos (shape-mor s) ------------> Q.Pos s
    --               |                           |
    --               |                           |
    -- symm-pres s σ |                           | σ
    --               |                           |
    --               v                           v
    --      R.Pos (shape-mor s) ------------> Q.Pos s
    --                           pos-mor s

unquoteDecl PremorphismIsoΣ = declareRecordIsoΣ PremorphismIsoΣ (quote Premorphism)

instance
  PremorphismToΣ : ∀ {ℓ} {Q R : QCont ℓ} {shape-mor : Q .QCont.Shape → R .QCont.Shape} → RecordToΣ (Premorphism Q R shape-mor)
  PremorphismToΣ = toΣ PremorphismIsoΣ

record PremorphismEquiv {ℓ} {Q R : QCont ℓ}
  {shape-mor : Q .QCont.Shape → R .QCont.Shape}
  (f g : Premorphism Q R shape-mor)
  : Type ℓ where

  private
    module Q = QCont Q
    module R = QCont R
    open Premorphism

  --                           η(s)
  --  R.Symm (shape-mor s) -----------> R.Symm (shape-mor s)
  --           |                                |
  --      f(s) |                                | g(s)
  --           '----------> Q.Symm s <----------'
  field
    η : (s : Q.Shape) → R.Symm (shape-mor s)
    η-comm : ∀ s → f .pos-mor s ≡ (η s R.◁ g .pos-mor s)

private
  variable
    ℓ : Level
    Q R S T : QCont ℓ

open QCont

open Premorphism

isSetPremorphism : {shape-mor : Q .Shape → R .Shape} → isSet (Premorphism Q R shape-mor)
isSetPremorphism {Q} {R} {shape-mor} = recordIsOfHLevel 2 $
  isSetΣ (isSetΠ2 (λ _ _ → Q .is-set-pos _))
  λ pos-mor → isSetΣSndProp (isSetΠ2 λ _ _ → isSetSymm R)
  λ symm-pres → isPropΠ2 λ _ _ → isOfHLevelPath' 1 (isSetΠ λ _ → Q .is-set-pos _) _ _

module _ (Q : QCont ℓ) where
  private
    module Q = QCont Q

  idPremorphism : Premorphism Q Q (id _)
  idPremorphism .pos-mor = id ∘ Q.Pos
  idPremorphism .symm-pres = id ∘ Q.Symm
  idPremorphism .symm-pres-natural _ _ = refl

isReflPremorphismEquiv : ∀ {shape-mor : Q .Shape → R .Shape} → (f : Premorphism Q R shape-mor) → PremorphismEquiv f f
isReflPremorphismEquiv {Q} {R} {shape-mor} f = go where
  module Q = QCont Q
  module R = QCont R
  η : (s : Q.Shape) → R.Symm (shape-mor s)
  η = R.SymmGroup.1g ∘ shape-mor

  go : PremorphismEquiv f f
  go .PremorphismEquiv.η = η
  go .PremorphismEquiv.η-comm s = refl


PremorphismPath : ∀ {shape-mor : Q .QCont.Shape → R .QCont.Shape} {f g : Premorphism Q R shape-mor}
  → (f .pos-mor ≡ g .pos-mor)
  → (f .symm-pres ≡ g .symm-pres)
  → f ≡ g
PremorphismPath {Q} {R} {shape-mor} {f} {g} pos-mor-path symm-pres-path i = λ
  { .pos-mor → pos-mor-path i
  ; .symm-pres → symm-pres-path i
  ; .symm-pres-natural s σ → isProp→PathP
    {B = λ i → pos-mor-path i s Q.▷ σ ≡ (symm-pres-path i s σ) R.◁ (pos-mor-path i s)}
    (λ i → isOfHLevelPath' 1 (isSet→ (Q.is-set-pos s)) _ _) (f .symm-pres-natural s σ) (g .symm-pres-natural s σ) i
  }
  where private
    module Q = QCont Q
    module R = QCont R

module Composite
  {u : Q .Shape → R .Shape} {v : R .Shape → S .Shape}
  (f : Premorphism Q R u) (g : Premorphism R S v)
  where
  private
    module Q = QCont Q
    module R = QCont R
    module S = QCont S
  
  comp-pos-mor : ∀ s → S.Pos (u ⋆ v $ s) → Q.Pos s
  comp-pos-mor s = g .pos-mor (u s) ⋆ f .pos-mor s

  comp-pos-symm-pres : ∀ s (σ : Q.Symm s) → S.Symm (u ⋆ v $ s)
  comp-pos-symm-pres s σ = g .symm-pres (u s) $ (f .symm-pres s σ)

  opaque
    compPremorphism-symm-pres-natural : ∀ s (σ : Q.Symm s) → (comp-pos-mor s) Q.▷ σ ≡ (comp-pos-symm-pres s σ) S.◁ (comp-pos-mor s)
    compPremorphism-symm-pres-natural s σ =
      g .pos-mor (u s) ⋆ f .pos-mor s ⋆ σ Q.⁺ ≡⟨ cong (g .pos-mor _ ⋆_) (f .symm-pres-natural s σ) ⟩
      g .pos-mor (u s) ⋆ f .symm-pres s σ R.⁺ ⋆ f .pos-mor s ≡⟨ cong (_⋆ f .pos-mor s) (g .symm-pres-natural (u s) (f .symm-pres s σ)) ⟩
      (g .symm-pres (u s) (f .symm-pres s σ)) S.⁺ ⋆ (g .pos-mor (u s) ⋆ f .pos-mor s) ∎

  compPremorphism : Premorphism Q S (u ⋆ v)
  compPremorphism .pos-mor = comp-pos-mor
  compPremorphism .symm-pres = comp-pos-symm-pres
  compPremorphism .symm-pres-natural = compPremorphism-symm-pres-natural

open Composite using () renaming (compPremorphism to _⋆-pre_)

opaque
  ⋆IdL : (u : Q .Shape → R .Shape) (f : Premorphism Q R u) → (idPremorphism Q) ⋆-pre f ≡ f
  ⋆IdL u f = PremorphismPath refl refl

  ⋆IdR : (u : Q .Shape → R .Shape) (f : Premorphism Q R u) → f ⋆-pre (idPremorphism R) ≡ f
  ⋆IdR u f = PremorphismPath refl refl

  ⋆Assoc : (u : Q .Shape → R .Shape) (v : R .Shape → S .Shape) (w : S .Shape → T .Shape)
    → (f : Premorphism Q R u)
    → (g : Premorphism R S v)
    → (h : Premorphism S T w)
    → (f ⋆-pre g) ⋆-pre h ≡ f ⋆-pre (g ⋆-pre h)
  ⋆Assoc u v w f g h = PremorphismPath refl refl
