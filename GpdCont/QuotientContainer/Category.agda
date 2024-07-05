module GpdCont.QuotientContainer.Category where

open import GpdCont.Prelude
open import GpdCont.QuotientContainer.Base
open import GpdCont.QuotientContainer.Eval

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Instances.Functors using (FUNCTOR)

module _ (ℓ : Level) where
  open import GpdCont.QuotientContainer.Premorphism as PMorphism
  open import GpdCont.QuotientContainer.Morphism as QMorphism

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
