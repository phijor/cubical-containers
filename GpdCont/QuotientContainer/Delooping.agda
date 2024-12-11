open import GpdCont.QuotientContainer.Base as QC using (QCont)

module GpdCont.QuotientContainer.Delooping {ℓ} (Q : QCont ℓ) where

open import GpdCont.Prelude hiding (Lift)
open import GpdCont.GroupoidContainer.Base using (GCont ; mkGCont)
open import GpdCont.GroupAction.AssociatedBundle using (associatedBundle)
import      GpdCont.Delooping

open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base

private
  module Q = QCont Q

  𝔹 : (G : Group ℓ) → Type ℓ
  𝔹  = uncurry GpdCont.Delooping.𝔹

  module 𝔹 {s : Q.Shape} = GpdCont.Delooping (Q.Symm s) (Q.SymmGroupStr s)

DeloopingShape : hGroupoid ℓ
DeloopingShape .fst = Σ[ s ∈ Q.Shape ] 𝔹 (Q.SymmGroup s)
DeloopingShape .snd = isGroupoidΣ (isSet→isGroupoid Q.is-set-shape) λ s → 𝔹.isGroupoid𝔹

DeloopingPos : ⟨ DeloopingShape ⟩ → hSet ℓ
DeloopingPos = uncurry λ s → associatedBundle (Q.symmAction s)

QContDelooping : GCont ℓ
QContDelooping = mkGCont DeloopingShape DeloopingPos
