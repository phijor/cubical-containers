module GpdCont.QuotientContainer.Category where

open import GpdCont.Prelude
open import GpdCont.Univalence using (ua→ua)
open import GpdCont.QuotientContainer.Base
open import GpdCont.QuotientContainer.Eval

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv using (funExt₂)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Instances.Functors using (FUNCTOR)
open import Cubical.Categories.Instances.Functors.Endo using (EndofunctorCategory)
open import Cubical.Categories.NaturalTransformation as NT using (NatTrans)

open import GpdCont.QuotientContainer.Premorphism as PMorphism
open import GpdCont.QuotientContainer.Morphism as QMorphism

module _ (ℓ : Level) where

  QCONT : Category (ℓ-suc ℓ) ℓ
  QCONT = record
    { ob = QCont ℓ
    ; QMorphism renaming
      ( Morphism to Hom[_,_]
      ; isSetMorphism to isSetHom
      ; compQContMorphism to _⋆_
      ; idQCont to id
      )
    }

  {-
  isUnivalentQCONT : isUnivalent QCONT
  isUnivalentQCONT .isUnivalent.univ Q R = isoToIsEquiv the-iso where
    open QCont
    open Morphism
    the-iso : Iso (Q ≡ R) (CatIso QCONT Q R)
    the-iso .Iso.fun = _
    the-iso .Iso.inv cont-iso = path where
      open Σ cont-iso renaming (fst to α⁺ ; snd to is-iso-α⁺)
      open isIso is-iso-α⁺ using () renaming (inv to α⁻ ; sec to α⁻-sec ; ret to α⁻-ret)

      shape-path : Q .Shape ≡ R .Shape
      shape-path = isoToPath (iso (α⁺ .shape-mor) (α⁻ .shape-mor) (λ r i → shape-mor (α⁻-sec i) r) (λ q i → shape-mor (α⁻-ret i) q))

      pos-path : PathP (λ i → shape-path i → Type _) (Q .Pos) (R .Pos)
      pos-path = ua→ λ q → isoToPath (iso {!α⁺ .pos-equiv !} {! !} {! !} {! !})

      path : Q ≡ R
      path i .QCont.Shape = shape-path i
      path i .QCont.Pos = pos-path i
      path i .QCont.isSymm = {! !}
      path i .QCont.is-set-shape = {! !}
      path i .QCont.is-set-pos = {! !}
      path i .QCont.is-prop-symm = {! !}
      path i .QCont.symm-id = {! !}
      path i .QCont.symm-sym = {! !}
      path i .QCont.symm-comp = {! !}
    the-iso .Iso.rightInv = {! !}
    the-iso .Iso.leftInv = {! !}
  -}

private
  variable
    ℓ : Level

  Endo : ∀ {ℓo ℓh} (C : Category ℓo ℓh) → Type _
  Endo C = Functor C C

Eval : (Q : QCont ℓ) → Endo (SET ℓ)
Eval Q = ⟦-⟧-functor where
  ⟦-⟧-functor : Functor (SET _) (SET _)
  ⟦-⟧-functor .Functor.F-ob = ⟦ Q ⟧
  ⟦-⟧-functor .Functor.F-hom {x = X} {y = Y} = ⟦ Q ⟧-map {X} {Y}
  ⟦-⟧-functor .Functor.F-id {x = X} = ⟦ Q ⟧-map-id X
  ⟦-⟧-functor .Functor.F-seq {x = X}  {y = Y} {z = Z} = ⟦ Q ⟧-map-comp {X} {Y} {Z}

module ⟦-⟧-hom (Q R : QCont ℓ) (open QCont) (u : Q .Shape → R .Shape) (f* : Premorphism Q R u) where
  private
    module Q = QCont Q
    module R = QCont R

    f : ∀ {s} → R.Pos (u s) → Q.Pos s
    f {s} = f* .Premorphism.pos-mor s

    module _ (X : hSet ℓ) where
      on-label : ∀ {s} → (Q.Pos s → ⟨ X ⟩) → ⟨ ⟦ R ⟧ X ⟩
      on-label label = Label→⟦ R ⟧ᵗ (label ∘ f)

      opaque
        on-label-equiv : ∀ {s} (l₀ l₁ : Q.Pos s → ⟨ X ⟩)
          → LabelEquiv Q s ⟨ X ⟩ l₀ l₁
          → LabelEquiv R (u s) ⟨ X ⟩ (l₀ ∘ f) (l₁ ∘ f)
        on-label-equiv {s} l₀ l₁ l₀∼l₁ =
          do
            (ψ , l₀≡l₁∘ψ) ← l₀∼l₁
            (ρ , ψ∘f≡f∘ρ) ← f* .Premorphism.symm-pres _ ψ
            let goal : (l₀ ∘ f) ≡ (l₁ ∘ f) ∘ ((ρ R.⁺))
                goal =
                  l₀ ∘ f          ≡⟨ cong (_∘ f) (funExt (ua→⁻ l₀≡l₁∘ψ)) ⟩
                  l₁ ∘ ψ Q.⁺ ∘ f  ≡⟨ cong (l₁ ∘_) ψ∘f≡f∘ρ ⟩
                  l₁ ∘ f ∘ ρ R.⁺ ∎
            return (ρ , ua→ (funExt⁻ goal))
          where
            open import Cubical.HITs.PropositionalTruncation.Monad

      on-label-well-defined : ∀ {s} (l₀ l₁ : Q.Pos s → ⟨ X ⟩)
        → LabelEquiv Q _ ⟨ X ⟩ l₀ l₁
        → on-label l₀ ≡ on-label l₁
      on-label-well-defined l₀ l₁ l₀∼l₁ = LabelEquiv→⟦ R ⟧Path (l₀ ∘ f) (l₁ ∘ f) $ on-label-equiv l₀ l₁ l₀∼l₁

  component : (X : hSet _) → ⟨ ⟦ Q ⟧ X ⟩ → ⟨ ⟦ R ⟧ X ⟩
  component X = ⟦ Q ⟧ᵗ-rec (isSet-⟦ R ⟧ᵗ ⟨ X ⟩) (on-label X) (on-label-well-defined X)

  opaque
    component-is-natural : (X Y : hSet _) → (g : ⟨ X ⟩ → ⟨ Y ⟩) → ⟦ Q ⟧-map {X = X} {Y = Y} g ⋆ (component Y) ≡ (component X) ⋆ ⟦ R ⟧-map {X = X} {Y = Y} g
    component-is-natural X Y g = funExt $
      ⟦ Q ⟧ᵗ-elimProp (λ _ → isSet-⟦ R ⟧ᵗ ⟨ Y ⟩ _ _)
        λ {s} label → refl {x = Label→⟦ R ⟧ᵗ (f ⋆ label ⋆ g)}

⟦-⟧-hom : (Q R : QCont ℓ) → QMorphism.Morphism Q R → NatTrans (Eval Q) (Eval R)
⟦-⟧-hom Q R = MorphismRec NT.isSetNatTrans go go-well-defined where
  open Premorphism using (pos-mor ; symm-pres)
  module Q = QCont Q
  module R = QCont R

  go : ∀ u → (Premorphism Q R u) → NatTrans (Eval Q) (Eval R)
  go u f = NT.natTrans component (λ {X} {Y} → component-is-natural X Y) where
    open ⟦-⟧-hom Q R u f using (component ; component-is-natural)

  opaque
    go-well-defined : ∀ {u} (f f′ : Premorphism Q R u) → PremorphismEquiv f f′ → go u f ≡ go u f′
    go-well-defined {u} f f′ f∼f′ = NT.makeNatTransPath $ funExt₂ λ X → ⟦ Q ⟧ᵗ-elimProp (λ _ → isSet-⟦ R ⟧ᵗ ⟨ X ⟩ _ _) (goal X) where
      module _ (X : hSet _) {s} (label : Q.Pos s → ⟨ X ⟩) where
        open import Cubical.HITs.PropositionalTruncation.Monad

        l∘f∼l∘f′ : LabelEquiv R (u s) ⟨ X ⟩ (label ∘ f .pos-mor s) (label ∘ f′ .pos-mor s)
        l∘f∼l∘f′ = do
          -- f and f′ are equivalent premorphisms, by induction on the evidence
          -- we obtain a (ρ : R.Symm (u s)) that relates f and f′.
          (ρ , f≡f′∘ρ) ← (f∼f′ s)
          let
            -- Postcomposing with the label, we see that ρ also relates (label ∘ f) and (label ∘ f′).
            l∘f≡l∘f′∘ρ : label ∘ (f .pos-mor _) ≡ label ∘ (f′ .pos-mor _) ∘ (ρ R.⁺)
            l∘f≡l∘f′∘ρ = cong (label ∘_) f≡f′∘ρ
          ∃-intro ρ $ ua→ $ funExt⁻ l∘f≡l∘f′∘ρ

        goal : Label→⟦ R ⟧ᵗ (label ∘ f .pos-mor s) ≡ Label→⟦ R ⟧ᵗ (label ∘ f′ .pos-mor s)
        goal = LabelEquiv→⟦ R ⟧Path _ _ l∘f∼l∘f′

opaque
  ⟦-⟧-hom-id : (Q : QCont ℓ) → ⟦-⟧-hom Q Q idQCont ≡ NT.idTrans (Eval Q)
  ⟦-⟧-hom-id Q = NT.makeNatTransPath $ funExt₂ λ X → ⟦ Q ⟧ᵗ-elimProp (λ _ → isSet-⟦ Q ⟧ᵗ ⟨ X ⟩ _ _) λ label → refl {x = Label→⟦ Q ⟧ᵗ label}

  ⟦-⟧-hom-comp : (Q R S : QCont ℓ) (f : QCONT ℓ [ Q , R ]) (g : QCONT ℓ [ R , S ])
    → ⟦-⟧-hom Q S (f ⋆⟨ QCONT _ ⟩ g) ≡ (⟦-⟧-hom Q R f) ⋆⟨ EndofunctorCategory (SET ℓ) ⟩ (⟦-⟧-hom R S g)
  ⟦-⟧-hom-comp Q R S f g = NT.makeNatTransPath $ funExt₂ λ X → ⟦ Q ⟧ᵗ-elimProp (λ _ → isSet-⟦ S ⟧ᵗ ⟨ X ⟩ _ _) λ label → {! !}

EvalFunctor : Functor (QCONT ℓ) (EndofunctorCategory (SET ℓ))
EvalFunctor .Functor.F-ob = Eval
EvalFunctor .Functor.F-hom = ⟦-⟧-hom _ _
EvalFunctor .Functor.F-id = ⟦-⟧-hom-id _
EvalFunctor .Functor.F-seq = ⟦-⟧-hom-comp _ _ _
