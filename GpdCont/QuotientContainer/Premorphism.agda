module GpdCont.QuotientContainer.Premorphism where

open import GpdCont.Prelude
open import GpdCont.QuotientContainer.Base

open import Cubical.Foundations.HLevels
import      Cubical.HITs.PropositionalTruncation as PT

module _ {ℓ} (Q R : QCont ℓ) (shape-mor : Q .QCont.Shape → R .QCont.Shape) where
  private
    module Q = QCont Q
    module R = QCont R

  isNaturalFiller : (f : ∀ s → R.Pos (shape-mor s) → Q.Pos s)
    → ∀ {s} (g : Q.Symm s) (h : R.Symm (shape-mor s))
    → Type _
  isNaturalFiller f {s} g h = (f s Q.▷ g) ≡ (h R.◁ f s)

  record Premorphism : Type ℓ where
    no-eta-equality

    field
      pos-mor : ∀ (s : Q.Shape) → R.Pos (shape-mor s) → Q.Pos s

    field
      symm-pres : ∀ (s : Q.Shape) (g : Q.Symm s) → ∃[ h ∈ (R.Symm (shape-mor s)) ] isNaturalFiller pos-mor g h
      -- The morphism of shapes preserves the subgroup of symmetries, naturally:
      --
      --                        pos-mor s
      --  R.Pos (shape-mor s) ------------> Q.Pos s
      --           |                           |
      --           |                           |
      --         h |                           | g
      --           |                           |
      --           v                           v
      --  R.Pos (shape-mor s) ------------> Q.Pos s
      --                        pos-mor s

unquoteDecl PremorphismIsoΣ = declareRecordIsoΣ PremorphismIsoΣ (quote Premorphism)

instance
  PremorphismToΣ : ∀ {ℓ} {Q R : QCont ℓ} {shape-mor : Q .QCont.Shape → R .QCont.Shape} → RecordToΣ (Premorphism Q R shape-mor)
  PremorphismToΣ {Q} {R} = toΣ PremorphismIsoΣ

module _ {ℓ} {Q R : QCont ℓ}  {shape-mor : Q .QCont.Shape → R .QCont.Shape} (f g : Premorphism Q R shape-mor) where
  private
    module Q = QCont Q
    module R = QCont R
    open Premorphism

  record PremorphismEquiv∞ : Type ℓ where
    --                          η(s)
    --  R.Pos (shape-mor s) -----------> R.Pos (shape-mor s)
    --          |                                |
    --     f(s) |                                | g(s)
    --          '-----------> Q.Pos s <----------'
    field
      η : (s : Q.Shape) → R.Symm (shape-mor s)
      η-comm : ∀ s → f .pos-mor s ≡ (η s R.◁ g .pos-mor s)
  
  PremorphismEquiv : Type ℓ
  PremorphismEquiv = ∀ (s : Q.Shape) → ∃[ ρ ∈ R.Symm (shape-mor s) ] f .pos-mor s ≡ ρ R.◁ g .pos-mor s

private
  variable
    ℓ : Level
    Q R S T : QCont ℓ

open QCont

open Premorphism

module _ {ℓ} {Q R : QCont ℓ} where
  private
    module R = QCont R
  PremorphismEquiv' : {u u′ : Q .Shape → R .Shape} → (f : Premorphism Q R u) → (f′ : Premorphism Q R u′) → Type _
  PremorphismEquiv' {u} {u′} f f′ =
    Σ[ p ∈ u ≡ u′ ]
      ∀ s → ∃[ ρ ∈ R.Symm (u s) ] (f .pos-mor s ≡ (ρ R.⁺) ⋆ r p ⋆ f′ .pos-mor s)
    where
      r : (p : u ≡ u′) → ∀ {s} → R .Pos (u s) → R .Pos (u′ s)
      r p = subst (R .Pos) (funExt⁻ p _)

opaque
  private
    isPropSymmPres : {shape-mor : Q .Shape → R .Shape} (pos-mor : ∀ s → R .Pos (shape-mor s) → Q .Pos s) → isProp (∀ (s : Q .Shape) → (g : Symm Q s) → ∃[ h ∈ (Symm R (shape-mor s)) ] isNaturalFiller Q R _ pos-mor g h)
    isPropSymmPres pos-mor = isPropΠ2 λ s g → isProp∃ _ _

  isSetPremorphism : {shape-mor : Q .Shape → R .Shape} → isSet (Premorphism Q R shape-mor)
  isSetPremorphism {Q} {R} {shape-mor} = recordIsOfHLevel 2 $
    isSetΣSndProp (isSetΠ2 (λ _ _ → Q .is-set-pos _)) $
    isPropSymmPres {Q = Q} {R = R}

module _ (Q : QCont ℓ) where
  private
    module Q = QCont Q

  idPremorphism : Premorphism Q Q (id _)
  idPremorphism .pos-mor = id ∘ Q.Pos
  idPremorphism .symm-pres s g = ∃-intro g refl

isReflPremorphismEquiv : ∀ {shape-mor : Q .Shape → R .Shape} → (f : Premorphism Q R shape-mor) → PremorphismEquiv f f
isReflPremorphismEquiv {Q} {R} {shape-mor} f = λ s → ∃-intro (ρ s) refl where
  module Q = QCont Q
  module R = QCont R
  ρ : (s : Q.Shape) → R.Symm (shape-mor s)
  ρ = R.SymmGroup.1g ∘ shape-mor


PremorphismPath : ∀ {shape-mor : Q .QCont.Shape → R .QCont.Shape} {f g : Premorphism Q R shape-mor}
  → (f .pos-mor ≡ g .pos-mor)
  → f ≡ g
PremorphismPath {Q} {R} {shape-mor} {f} {g} pos-mor-path = λ
  { i .pos-mor → pos-mor-path i
  ; i .symm-pres → isProp→PathP (λ i → isPropSymmPres {Q = Q} {R = R} (pos-mor-path i)) (f .symm-pres) (g .symm-pres) i
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

  compPremorphism : Premorphism Q S (u ⋆ v)
  compPremorphism .pos-mor = comp-pos-mor
  compPremorphism .symm-pres s ψ = goal where
    open import Cubical.HITs.PropositionalTruncation.Monad using (_>>=_ ; return)

    opaque
      lem : (ρ : R.Symm _) → isNaturalFiller Q R u (f .pos-mor) ψ ρ
        → (σ : S.Symm _) → isNaturalFiller R S v (g .pos-mor) ρ σ
        → isNaturalFiller Q S (u ⋆ v) comp-pos-mor ψ σ
      lem ρ ρ-nat σ σ-nat =
        g .pos-mor _ ⋆ f .pos-mor _ ⋆ (ψ Q.⁺) ≡⟨ cong (g .pos-mor _ ⋆_) ρ-nat ⟩
        g .pos-mor _ ⋆ (ρ R.⁺) ⋆ f .pos-mor _ ≡⟨ cong (_⋆ f .pos-mor _) σ-nat ⟩
        (σ S.⁺) ⋆ g .pos-mor _ ⋆ f .pos-mor _ ∎

      goal : ∃[ τ ∈ S.Symm _ ] isNaturalFiller Q S (u ⋆ v) comp-pos-mor ψ τ
      goal = do
        (ρ , ρ-nat) ← (f .symm-pres s ψ)
        (σ , σ-nat) ← (g .symm-pres (u s) ρ)
        return $ σ , lem ρ ρ-nat σ σ-nat

open Composite using () renaming (compPremorphism to _⋆-pre_)

opaque
  ⋆IdL : (u : Q .Shape → R .Shape) (f : Premorphism Q R u) → (idPremorphism Q) ⋆-pre f ≡ f
  ⋆IdL u f = PremorphismPath refl

  ⋆IdR : (u : Q .Shape → R .Shape) (f : Premorphism Q R u) → f ⋆-pre (idPremorphism R) ≡ f
  ⋆IdR u f = PremorphismPath refl

  ⋆Assoc : (u : Q .Shape → R .Shape) (v : R .Shape → S .Shape) (w : S .Shape → T .Shape)
    → (f : Premorphism Q R u)
    → (g : Premorphism R S v)
    → (h : Premorphism S T w)
    → (f ⋆-pre g) ⋆-pre h ≡ f ⋆-pre (g ⋆-pre h)
  ⋆Assoc u v w f g h = PremorphismPath refl
