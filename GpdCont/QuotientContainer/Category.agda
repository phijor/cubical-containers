module GpdCont.QuotientContainer.Category where

open import GpdCont.Prelude
open import GpdCont.QuotientContainer.Base
open import GpdCont.QuotientContainer.Morphism
open import GpdCont.QuotientContainer.Eval

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Instances.Functors using (FUNCTOR)

module _ (ℓ : Level) where
  QCONT : Category (ℓ-suc ℓ) ℓ
  QCONT .Category.ob = QCont ℓ
  QCONT .Category.Hom[_,_] = QContMorphism
  QCONT .Category.id = QContId _
  QCONT .Category._⋆_ = compQContMorphism
  QCONT .Category.⋆IdL = {! !}
  QCONT .Category.⋆IdR = {! !}
  QCONT .Category.⋆Assoc = {! !}
  QCONT .Category.isSetHom = isSetQContMorphism

private
  variable
    ℓ : Level

  Endo : ∀ {ℓo ℓh} (C : Category ℓo ℓh) → Type _
  Endo C = Functor C C

Eval : (Q : QCont ℓ) → Endo (SET ℓ)
Eval Q = ⟦-⟧-functor where
  ⟦-⟧-functor : Functor (SET _) (SET _)
  ⟦-⟧-functor .Functor.F-ob = ⟦ Q ⟧
  ⟦-⟧-functor .Functor.F-hom = ⟦ Q ⟧-map
  ⟦-⟧-functor .Functor.F-id = ⟦ Q ⟧-map-id _
  ⟦-⟧-functor .Functor.F-seq = ⟦ Q ⟧-map-comp
