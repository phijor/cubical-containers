{-# OPTIONS --lossy-unification #-}
open import GpdCont.QuotientContainer.Base as QC using (QCont)

module GpdCont.QuotientContainer.Delooping {ℓ} (Q : QCont ℓ) where

open import GpdCont.Prelude hiding (Lift)
open import GpdCont.GroupoidContainer.Base using (GCont ; mkGCont)
open import GpdCont.GroupAction.AssociatedBundle using (associatedBundle)
open import GpdCont.GroupAction.Faithful using (isFaithful→isSetTruncAssociatedBundle)
import      GpdCont.Delooping

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base
open import Cubical.Data.Sigma using (Σ-assoc-≃)

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

hasSetFibersDeloopingPos : (Y : hSet ℓ) → isSet (fiber DeloopingPos Y)
hasSetFibersDeloopingPos Y = isOfHLevelRespectEquiv 2 fiber-equiv isSet-Σfiber where
  fiber-equiv : (Σ[ s ∈ Q.Shape ] fiber (associatedBundle (Q.symmAction s)) Y) ≃ fiber DeloopingPos Y

  isSet-Σfiber : isSet (Σ[ s ∈ Q.Shape ] fiber (associatedBundle (Q.symmAction s)) Y)
  isSet-Σfiber = isSetΣ
    Q.is-set-shape
    λ s → isFaithful→isSetTruncAssociatedBundle (Q.isFaithfulSymmAction s) Y

  fiber-equiv = invEquiv (Σ-assoc-≃ {A = Q.Shape} {B = λ s → 𝔹 (Q.SymmGroup s)} {C = λ s x → associatedBundle (Q.symmAction s) x ≡ Y})
