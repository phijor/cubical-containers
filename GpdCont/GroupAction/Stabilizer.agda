open import GpdCont.Prelude
open import GpdCont.Univalence
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.AssociatedBundle
import      GpdCont.Delooping as Delooping

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base

module GpdCont.GroupAction.Stabilizer {ℓX ℓG} {X : hSet ℓX} {G : Group ℓG} (σ : Action G X) where

private
  module G = GroupStr (str G)
  module 𝔹G = Delooping G
  module σ where
    open Action σ public
    open ActionProperties σ public

module _ (x : ⟨ X ⟩) where
  isStabilizer : ⟨ G ⟩ → Type _
  isStabilizer g = PathP (λ i → ua (σ.action g) i) x x

  isPropIsStabilizer : ∀ g → isProp (isStabilizer g)
  isPropIsStabilizer g = isOfHLevelPathP' 1 (str X) x x

  mkIsStabilizer : ∀ {g} → g σ.▷ x ≡ x → isStabilizer g
  mkIsStabilizer {g} = ua-gluePath (σ.action g)

  getIsStabilizer : ∀ {g} → isStabilizer g → g σ.▷ x ≡ x
  getIsStabilizer {g} = ua-ungluePath (σ.action g)

  opaque
    isStabilizer-1g : isStabilizer G.1g
    isStabilizer-1g = mkIsStabilizer (σ.action-1-id ≡$ x)

    isStabilizer-· : ∀ {g h} → isStabilizer g → isStabilizer h → isStabilizer (g G.· h)
    isStabilizer-· {g} {h} stab-g stab-h = mkIsStabilizer $
      (g G.· h) σ.▷ x ≡⟨ σ.action-comp g h ≡$ x ⟩
      h σ.▷ (g σ.▷ x) ≡⟨ cong (h σ.▷_) $ getIsStabilizer stab-g ⟩
      h σ.▷ x ≡⟨ getIsStabilizer stab-h ⟩
      x ∎

    isStabilizer-inv : ∀ {g} → isStabilizer g → isStabilizer (G.inv g)
    isStabilizer-inv {g} stab-g = mkIsStabilizer $
      G.inv g σ.▷ x ≡⟨ σ.action-inv g ≡$ x ⟩
      invEq (σ.action g) x ≡⟨ sym $ (invEq $ equivAdjointEquiv (σ.action g)) (getIsStabilizer stab-g) ⟩
      x ∎

  StabSet : hSet _
  StabSet .fst = Σ[ g ∈ ⟨ G ⟩ ] (isStabilizer g)
  StabSet .snd = isSetΣSndProp G.is-set isPropIsStabilizer

  StabSet≡ : ∀ {g h : ⟨ StabSet ⟩} → g .fst ≡ h .fst → g ≡ h
  StabSet≡ = Σ≡Prop isPropIsStabilizer

  Stab : Group _
  Stab .fst = ⟨ StabSet ⟩
  Stab .snd .GroupStr.1g .fst = G.1g
  Stab .snd .GroupStr.1g .snd = isStabilizer-1g
  Stab .snd .GroupStr._·_ (g , stab-g) (h , stab-h) .fst = g G.· h
  Stab .snd .GroupStr._·_ (g , stab-g) (h , stab-h) .snd = isStabilizer-· stab-g stab-h
  Stab .snd .GroupStr.inv (g , stab-g) .fst = G.inv g
  Stab .snd .GroupStr.inv (g , stab-g) .snd = isStabilizer-inv stab-g
  Stab .snd .GroupStr.isGroup = makeIsGroup (str StabSet)
    (λ g h k → StabSet≡ (G.·Assoc _ _ _))
    (λ g → StabSet≡ (G.·IdR _))
    (λ g → StabSet≡ (G.·IdL _))
    (λ g → StabSet≡ (G.·InvR _))
    (λ g → StabSet≡ (G.·InvL _))

  module Stab = GroupStr (str Stab)

invariantEquiv : ((x : Delooping.𝔹 G) → ⟨ associatedBundle σ x ⟩) ≃ (Σ[ x ∈ ⟨ X ⟩ ] ∀ g → isStabilizer x g)
invariantEquiv = invEquiv (𝔹G.elimSetEquiv (str ∘ associatedBundle σ))
