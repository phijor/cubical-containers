module GpdCont.Group.SemidirectProduct where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import GpdCont.Prelude hiding (_▷_)
open import GpdCont.HomotopySet
open import GpdCont.Group.Opposite
open import GpdCont.GroupAction.Base

private
  Group→hSet : ∀ {ℓ} → (H : Group ℓ) → hSet ℓ
  Group→hSet H .fst = ⟨ H ⟩
  Group→hSet H .snd = str H .GroupStr.is-set


Aut : ∀ {ℓ} → (G : Group ℓ) → Group ℓ
Aut G .fst = GroupEquiv G G
Aut G .snd .GroupStr.1g = idGroupEquiv
Aut G .snd .GroupStr._·_ = compGroupEquiv
Aut G .snd .GroupStr.inv = invGroupEquiv
Aut G .snd .GroupStr.isGroup = makeIsGroup is-set-aut
  (λ α β γ → GroupEquiv≡ (compEquiv-assoc _ _ _))
  (λ α → GroupEquiv≡ (compEquivEquivId _))
  (λ α → GroupEquiv≡ (compEquivIdEquiv _))
  (λ α → GroupEquiv≡ (invEquiv-is-rinv _))
  (λ α → GroupEquiv≡ (invEquiv-is-linv _))
  where
    module G = GroupStr (str G)

    is-set-aut : isSet (GroupEquiv G G)
    is-set-aut = isSetΣSndProp (isOfHLevel≃ 2 G.is-set G.is-set) λ _ → isPropIsGroupHom _ _


module AutHom {ℓN ℓH} (N : Group ℓN) (H : Group ℓH) (φ : GroupHom (H ᵒᵖ) (Aut N)) where
  module hom = IsGroupHom (φ .snd)

  ac : Action (H ᵒᵖ) (Group→hSet N)
  ac .Action.action h = φ .fst h .fst
  ac .Action.pres· h₀ h₁ = cong fst $ hom.pres· h₀ h₁

  open Action ac public using (_▷_ ; _▷⁻_)
  open ActionProperties ac public

  module at h = IsGroupHom (φ .fst h .snd)

module _ {ℓN ℓH} (N : Group ℓN) (H : Group ℓH) (φ : GroupHom (H ᵒᵖ) (Aut N)) where

  private
    G = ⟨ N ⟩ × ⟨ H ⟩

    G≡ : {g h : G} → g .snd ≡ h .snd → g .fst ≡ h .fst → g ≡ h
    G≡ = flip ≡-×

    module N = GroupStr (str N)
    module H = GroupStr (str H)
    module φ where
      module hom = IsGroupHom (φ .snd)

      ac : Action (H ᵒᵖ) (Group→hSet N)
      ac .Action.action h = φ .fst h .fst
      ac .Action.pres· h₀ h₁ = cong fst $ hom.pres· h₀ h₁

      open Action ac public using (_▷_ ; _▷⁻_)
      open ActionProperties ac public

      module at h = IsGroupHom (φ .fst h .snd)

    _·_ : G → G → G
    ((n₁ , h₁) · (n₂ , h₂)) .fst = n₁ N.· (h₁ φ.▷ n₂)
    ((n₁ , h₁) · (n₂ , h₂)) .snd = h₁ H.· h₂

    1g : G
    1g .fst = N.1g
    1g .snd = H.1g

    inv : G → G
    inv (n , h) .fst = (H.inv h) φ.▷ (N.inv n)
    inv (n , h) .snd = H.inv h

    opaque
      assoc : (g h k : G) → g · (h · k) ≡ (g · h) · k
      assoc (n₀ , h₀) (n₁ , h₁) (n₂ , h₂) = G≡ (H.·Assoc h₀ h₁ h₂) $
        n₀ N.· (h₀ φ.▷ (n₁ N.· (h₁ φ.▷ n₂)))
          ≡⟨ cong (n₀ N.·_) (φ.at.pres· h₀ n₁ (h₁ φ.▷ n₂)) ⟩
        n₀ N.· (h₀ φ.▷ n₁) N.· (h₀ φ.▷ (h₁ φ.▷ n₂))
          ≡⟨ cong (λ - → n₀ N.· (h₀ φ.▷ n₁) N.· -) (sym $ φ.action-comp-ext h₁ h₀ n₂) ⟩
        n₀ N.· (h₀ φ.▷ n₁) N.· ((h₀ H.· h₁) φ.▷ n₂)
          ≡⟨ N.·Assoc _ _ _ ⟩
        (n₀ N.· (h₀ φ.▷ n₁)) N.· ((h₀ H.· h₁) φ.▷ n₂)
          ∎

      id-right : (g : G) → g · 1g ≡ g
      id-right (n , h) = G≡ (H.·IdR h) $
        n N.· (h φ.▷ N.1g)
          ≡⟨ cong (n N.·_) (φ.at.pres1 h) ⟩
        n N.· N.1g
          ≡⟨ N.·IdR n ⟩
        n
          ∎

      id-left : (g : G) → 1g · g ≡ g
      id-left (n , h) = G≡ (H.·IdL h) $
        N.1g N.· (H.1g φ.▷ n)
          ≡⟨ cong (N.1g N.·_) (φ.action-1-id ≡$ n) ⟩
        N.1g N.· n
          ≡⟨ N.·IdL n ⟩
        n
          ∎

      inv-left : (x : G) → inv x · x ≡ 1g
      inv-left (n , h) = G≡ (H.·InvL h) $
        (H.inv h φ.▷ N.inv n) N.· (H.inv h φ.▷ n)
          ≡⟨ sym (φ.at.pres· (H.inv h) (N.inv n) n) ⟩
        (H.inv h φ.▷ (N.inv n N.· n))
          ≡⟨ cong (H.inv h φ.▷_) (N.·InvL n) ⟩
        (H.inv h φ.▷ N.1g)
          ≡⟨ φ.at.pres1 _ ⟩
        N.1g
          ∎

      inv-right : (x : G) → x · inv x ≡ 1g
      inv-right (n , h) = G≡ (H.·InvR h) $
        n N.· (h φ.▷ (H.inv h φ.▷ N.inv n))
          ≡⟨ cong (n N.·_) $ sym $ φ.action-comp-ext (H.inv h) h _ ⟩
        n N.· ((h H.· H.inv h) φ.▷ N.inv n)
          ≡⟨ cong (λ - → n N.· (- φ.▷ _)) $ H.·InvR h ⟩
        n N.· (H.1g φ.▷ N.inv n)
          ≡⟨ cong (n N.·_) $ φ.action-1-id ≡$ N.inv n ⟩
        n N.· N.inv n
          ≡⟨ N.·InvR _ ⟩
        N.1g
          ∎

  SemidirProd : Group (ℓ-max ℓN ℓH)
  SemidirProd .fst = G
  SemidirProd .snd .GroupStr.1g = 1g
  SemidirProd .snd .GroupStr._·_ = _·_
  SemidirProd .snd .GroupStr.inv = inv
  SemidirProd .snd .GroupStr.isGroup = makeIsGroup (isSet× N.is-set H.is-set)
    assoc
    id-right
    id-left
    inv-right
    inv-left

  SemidirProdContrBot : isContr ⟨ N ⟩ → GroupEquiv SemidirProd H
  SemidirProdContrBot = {! !}

⋊-syntax : ∀ {ℓN ℓH} (N : Group ℓN) (H : Group ℓH) → (φ : GroupHom (H ᵒᵖ) (Aut N)) → Group (ℓ-max ℓN ℓH)
⋊-syntax = SemidirProd

infix 10 ⋊-syntax
syntax ⋊-syntax N H φ = N ⋊[ φ ] H

module _
  {ℓN₀ ℓN₁ ℓH₀ ℓH₁}
  {N₀ : Group ℓN₀} {N₁ : Group ℓN₁}
  {H₀ : Group ℓH₀} {H₁ : Group ℓH₁}
  (φ₀ : GroupHom (H₀ ᵒᵖ) (Aut N₀))
  (φ₁ : GroupHom (H₁ ᵒᵖ) (Aut N₁))
  (ν* : GroupEquiv N₀ N₁)
  (η* : GroupEquiv H₀ H₁)
  where
  private
    ν = equivFun (ν* .fst)
    {-# INLINE ν #-}
    η = equivFun (η* .fst)
    {-# INLINE η #-}
    module ν = IsGroupHom (ν* .snd)
    module η = IsGroupHom (η* .snd)
    module N₀ = GroupStr (str N₀)
    module N₁ = GroupStr (str N₁)
    module H₀ = GroupStr (str H₀)
    module H₁ = GroupStr (str H₁)
    module φ₀ = AutHom N₀ H₀ φ₀
    module φ₁ = AutHom N₁ H₁ φ₁

  SemidirectProductEquiv :
    (p : ∀ n h → ν (h φ₀.▷ n) ≡ η h φ₁.▷ ν n)
    → GroupEquiv (N₀ ⋊[ φ₀ ] H₀) (N₁ ⋊[ φ₁ ] H₁)
  SemidirectProductEquiv p = goal where
    equiv : ⟨ N₀ ⟩ × ⟨ H₀ ⟩ ≃ ⟨ N₁ ⟩ × ⟨ H₁ ⟩
    equiv = ≃-× (ν* .fst) (η* .fst)

    opaque
      is-hom-equiv : IsGroupHom (str $ SemidirProd N₀ H₀ φ₀) (equivFun equiv) (str $ SemidirProd N₁ H₁ φ₁)
      is-hom-equiv = makeIsGroupHom goal where module _ ((n , h) (n' , h') : ⟨ SemidirProd N₀ H₀ φ₀ ⟩) where
        lem₁ : ν (n N₀.· (h φ₀.▷ n')) ≡ ν n N₁.· (η h φ₁.▷ ν n')
        lem₁ = ν.pres· _ _ ∙ cong (ν n N₁.·_) (p n' h)

        lem₂ : η (h H₀.· h') ≡ (η h) H₁.· (η h')
        lem₂ = η.pres· h h'

        goal : _ ≡ _
        goal = ΣPathP (lem₁ , lem₂)

    goal : GroupEquiv _ _
    goal .fst = equiv
    goal .snd = is-hom-equiv
