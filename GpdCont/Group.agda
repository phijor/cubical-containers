module GpdCont.Group where

open import GpdCont.Prelude
open import GpdCont.RecordEquiv

open import Cubical.Foundations.Structure
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

record GroupStr {ℓ} (G : Type ℓ) : Type ℓ where
  field
    is-connected : isContr ∥ G ∥₂
    is-groupoid : isGroupoid G
    pt : G

Group : (ℓ : Level) → Type _
Group ℓ = TypeWithStr ℓ GroupStr

unquoteDecl GroupStrIsoΣ = declareRecordIsoΣ GroupStrIsoΣ (quote GroupStr)

instance
  GroupStrToΣ : ∀ {ℓ} {G : Type ℓ} → RecordToΣ (GroupStr G)
  GroupStrToΣ = toΣ GroupStrIsoΣ

