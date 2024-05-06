module GpdCont.QuotientContainer.Morphism where

open import GpdCont.Prelude
open import GpdCont.QuotientContainer.Base
open import GpdCont.QuotientContainer.Premorphism as Premorphism using (Premorphism ; PremorphismEquiv)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.HITs.SetQuotients as SQ using (_/_)

private
  variable
    ℓ : Level
    Q R S T : QCont ℓ

open QCont

Premorphism/ : (Q R : QCont ℓ) (shape-mor : Q .Shape → R .Shape) → Type ℓ
Premorphism/ Q R shape-mor = Premorphism Q R shape-mor / PremorphismEquiv

pre-morphism-class : ∀ {u : Q .Shape → R .Shape} (f : Premorphism Q R u) → Premorphism/ Q R u
pre-morphism-class f = SQ.[ f ]

pre-morphism-eq/ : ∀ {u : Q .Shape → R .Shape} {f g : Premorphism Q R u} → PremorphismEquiv f g → pre-morphism-class f ≡ pre-morphism-class g
pre-morphism-eq/ {f} {g} f≈g = SQ.eq/ {R = PremorphismEquiv} f g f≈g

record Morphism {ℓ} (Q R : QCont ℓ) : Type ℓ where
  constructor mk-qcont-morphism
  pattern

  field
    shape-mor : Q .Shape → R .Shape
    pos-equiv : Premorphism/ Q R shape-mor

unquoteDecl MorphismIsoΣ = declareRecordIsoΣ MorphismIsoΣ (quote Morphism)

instance
  MorphismToΣ : ∀ {ℓ} {Q R : QCont ℓ} → RecordToΣ (Morphism Q R)
  MorphismToΣ = toΣ MorphismIsoΣ

isSetMorphism : isSet (Morphism Q R)
isSetMorphism {Q} {R} = recordIsOfHLevel 2 $
  isSetΣ isSet-shape-mor isSet-Premorphism/
  where
  private
    module Q = QCont Q
    module R = QCont R
  
  isSet-shape-mor : isSet (Q.Shape → R.Shape)
  isSet-shape-mor = isSet→ (QCont.is-set-shape R)

  isSet-Premorphism/ : ∀ shape-mor → isSet (Premorphism/ Q R shape-mor)
  isSet-Premorphism/ shape-mor = SQ.squash/

open Morphism
private
  pre→mor : ∀ {u : Q .Shape → R .Shape} (f : Premorphism Q R u) → Morphism Q R
  pre→mor {u = u} f .shape-mor = u
  pre→mor {u = u} f .pos-equiv = pre-morphism-class f

opaque
  MorphismElimProp : ∀ {ℓP} (P : Morphism Q S → Type ℓP)
    → (∀ α → isProp (P α))
    → ((u : Q .Shape → S .Shape) (f : Premorphism Q S u) → P (pre→mor f))
    → ∀ α → P α
  MorphismElimProp P is-prop-P p* α = SQ.elimProp {P = λ f → P (mk-qcont-morphism (α .shape-mor) f)}
    (is-prop-P ∘ (mk-qcont-morphism (α .shape-mor)))
    (p* (α .shape-mor))
    (α .pos-equiv)

  MorphismElimProp3 : ∀ {Q Q′ Q″ R R′ R″ : QCont ℓ} {ℓP} (P : Morphism Q R → Morphism Q′ R′ → Morphism Q″ R″ → Type ℓP)
    → (∀ α β γ → isProp (P α β γ))
    → (∀ u v w → (f : Premorphism Q R u) (g : Premorphism Q′ R′ v) (h : Premorphism Q″ R″ w) → P (pre→mor f) (pre→mor g) (pre→mor h))
    → ∀ α β γ → P α β γ
  MorphismElimProp3 P is-prop-P p* α β γ = SQ.elimProp3 {P = λ f g h → P (mk-qcont-morphism _ f) (mk-qcont-morphism _ g) (mk-qcont-morphism _ h)}
    (λ f g h → is-prop-P _ _ _)
    (p* _ _ _)
    (α .pos-equiv) (β .pos-equiv) (γ .pos-equiv)

idQCont : {Q : QCont ℓ} → Morphism Q Q
idQCont {Q} = pre→mor (Premorphism.idPremorphism Q)

compQContMorphism : (α : Morphism Q R) (β : Morphism R S) → Morphism Q S
compQContMorphism {Q} {R} {S} α β = composite where
  private
    module R = QCont R
    module S = QCont S

  open Premorphism.Composite {u = α .shape-mor} {v = β .shape-mor} using () renaming (compPremorphism to _⋆-pre_)

  composite : Morphism Q S
  composite .shape-mor = α .shape-mor ⋆ β .shape-mor
  composite .pos-equiv = SQ.rec SQ.squash/ (composite' (β .pos-equiv)) (well-defined (β .pos-equiv)) (α .pos-equiv) where

    open Premorphism.Premorphism
    open PremorphismEquiv
    opaque
      well-defined' : (f : Premorphism Q R (α .shape-mor)) (g g′ : Premorphism R S (β .shape-mor)) → PremorphismEquiv g g′ → PremorphismEquiv (f ⋆-pre g) (f ⋆-pre g′)
      well-defined' f g g′ g-equiv-g′ = λ where
        .η q → g-equiv-g′ .η (α .shape-mor q)
        .η-comm q →
          (f ⋆-pre g) .pos-mor q ≡⟨⟩
          (g .pos-mor _ ⋆ f .pos-mor _) ≡⟨ cong (_⋆ f .pos-mor _) (g-equiv-g′ .η-comm _) ⟩
          g-equiv-g′ .η (α .shape-mor q) S.⁺ ⋆ g′ .pos-mor _ ⋆ f .pos-mor _ ≡⟨⟩
          g-equiv-g′ .η (α .shape-mor q) S.◁ (f ⋆-pre g′) .pos-mor q ∎

    composite' : Premorphism/ R S (β .shape-mor) → Premorphism Q R (α .shape-mor) → Premorphism/ Q S (α .shape-mor ⋆ β .shape-mor)
    composite' [g] f = SQ.rec SQ.squash/ (λ g → pre-morphism-class (f ⋆-pre g)) (λ { g g′ r → pre-morphism-eq/ (well-defined' f g g′ r) }) [g]

    opaque
      well-defined : ([g] : Premorphism/ R S (β .shape-mor)) (f f′ : Premorphism Q R (α .shape-mor)) → PremorphismEquiv f f′ → composite' [g] f ≡ composite' [g] f′
      well-defined [g] f f′ f-equiv-f′ = SQ.elimProp {P = λ [g] → composite' [g] f ≡ composite' [g] f′} (λ [g] → SQ.squash/ _ _) (λ g → pre-morphism-eq/ $ comp-equiv g) [g] where
        comp-equiv : ∀ g → PremorphismEquiv (f ⋆-pre g) (f′ ⋆-pre g)
        comp-equiv g = λ where
          .η q → g .symm-pres (α .shape-mor q) (f-equiv-f′ .η q)
          .η-comm q →
            (f ⋆-pre g) .pos-mor q ≡⟨⟩
            g .pos-mor _ ⋆ f .pos-mor _ ≡⟨ cong (g .pos-mor _ ⋆_) (f-equiv-f′ .η-comm q) ⟩
            g .pos-mor _ ⋆ (f-equiv-f′ .η _ R.◁ f′ .pos-mor _) ≡⟨⟩
            (g .pos-mor _ R.▷ f-equiv-f′ .η _) ⋆ f′ .pos-mor _ ≡⟨ cong (_⋆ f′ .pos-mor _) $ g .symm-pres-natural _ (f-equiv-f′ .η q) ⟩
            (g .symm-pres _ (f-equiv-f′ .η q) S.◁ g .pos-mor (α .shape-mor q)) ⋆ f′ .pos-mor _ ≡⟨⟩
            (g .symm-pres _ (f-equiv-f′ .η q)) S.◁ (f′ ⋆-pre g) .pos-mor q ∎

private
  _⋆Q_ = compQContMorphism

opaque
  ⋆IdL : (α : Morphism Q S) → idQCont ⋆Q α ≡ α
  ⋆IdL = MorphismElimProp (λ α → idQCont ⋆Q α ≡ α) (λ α → isSetMorphism _ α)
    λ { u f → cong pre→mor (Premorphism.⋆IdL u f) }

  ⋆IdR : (α : Morphism Q S) → α ⋆Q idQCont ≡ α
  ⋆IdR = MorphismElimProp (λ α → α ⋆Q idQCont ≡ α) (λ α → isSetMorphism _ α)
    λ { u f → cong pre→mor (Premorphism.⋆IdR u f) }

  ⋆Assoc : (α : Morphism Q R) (β : Morphism R S) (γ : Morphism S T) → (α ⋆Q β) ⋆Q γ ≡ α ⋆Q (β ⋆Q γ)
  ⋆Assoc = MorphismElimProp3 _ (λ { _ _ _ → isSetMorphism _ _ })
    λ u v w f g h i → pre→mor (Premorphism.⋆Assoc u v w f g h i)
