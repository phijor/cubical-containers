-- TODO:
-- ⋆ Define `isSkeletal` as propositional truncation `Skeleton`
module GpdCont.Experimental.Groups.Skeleton where

open import GpdCont.Prelude
open import GpdCont.RecordEquiv
open import GpdCont.Experimental.Groups.Base
open import GpdCont.SetTruncation using (isConnected-fiber-∣-∣₂ ; componentEquiv)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (section ; retract ; Iso)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)

private
  variable
    ℓ : Level

record Skeleton (G* : hGroupoid ℓ) : Type (ℓ-suc ℓ) where
  private
    G = ⟨ G* ⟩

  Component : ∥ G ∥₂ → Type ℓ
  Component = fiber ∣_∣₂

  isGroupoidComponent : ∀ x → isGroupoid (Component x)
  isGroupoidComponent x = isGroupoidΣ (str G*) λ g → isProp→isOfHLevelSuc 2 (ST.squash₂ ∣ g ∣₂ x)

  field
    component-section : (x : ∥ G ∥₂) → Component x

  Index : Type ℓ
  Index = ∥ G ∥₂

  isSetIndex : isSet Index
  isSetIndex = ST.isSetSetTrunc

  Total : Type ℓ
  Total = Σ ∥ G ∥₂ (fiber ∣_∣₂)

  TotalEquiv : G ≃ Total
  TotalEquiv = componentEquiv G

  index-of : G → Index
  index-of = fst ∘ equivFun TotalEquiv

  isGroupoidTotal : isGroupoid Total
  isGroupoidTotal = isGroupoidΣ (isSet→isGroupoid ST.isSetSetTrunc) isGroupoidComponent

  sk : ∥ G ∥₂ → G
  sk = fst ∘ component-section

  sk-section : section ∣_∣₂ sk
  sk-section = snd ∘ component-section

  ComponentGroupStr : ∀ x → GroupStr (Component x)
  ComponentGroupStr x .GroupStr.is-connected = isConnected-fiber-∣-∣₂ x
  ComponentGroupStr x .GroupStr.is-groupoid = isGroupoidComponent x
  ComponentGroupStr x .GroupStr.pt = component-section x

  ComponentGroup : ∥ G ∥₂ → Group _
  ComponentGroup x = Component x , ComponentGroupStr x

  hasRetract : (∀ g → component-section ∣ g ∣₂ ≡ (g , refl)) → isSet G
  hasRetract retr = isOfHLevelRetract 2 ∣_∣₂ sk (cong fst ∘ retr) ST.isSetSetTrunc
