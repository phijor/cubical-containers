module GpdCont.Group.WreathProduct where

open import GpdCont.Prelude
open import GpdCont.Equiv
open import GpdCont.Embedding
open import GpdCont.HomotopySet
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Faithful
open import GpdCont.Group.Subgroup
open import GpdCont.Group.Opposite
open import GpdCont.Group.SemidirectProduct
open import GpdCont.PropositionalTruncation as PT using (∥_∥₁)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)
open import Cubical.Relation.Nullary using (¬_)


module Wreathᴰ {ℓX ℓG ℓH} (G : Group ℓG) (X : hSet ℓX) (σ : Action G X)
  (H : ⟨ X ⟩ → Group ℓH)
  (η : ∀ g x → ⟨ H x ⟩ ≃ ⟨ H (σ ⁺ g $ x) ⟩)
  (η' : ∀ g → PathP (λ i → ua (σ .Action.action g) i → Type _) (⟨_⟩ ∘ H) (⟨_⟩ ∘ H))
  where
  private
    ΠH : Group _
    ΠH = ΠGroup {X = ⟨ X ⟩} H

    ΠHSet : hSet _
    ΠHSet .fst = ⟨ ΠH ⟩
    ΠHSet .snd = str ΠH .GroupStr.is-set

    module G = GroupStr (str G)
    module H x = GroupStr (str (H x))
    module σ where
      open Action σ public
      open ActionProperties σ public

    --
    φ' : Action G ΠHSet
    φ' .Action.action g = isoToEquiv (iso (λ h x → invEq (η g x) (h (g σ.▷ x))) (λ { h x → {! equivFun (η _ ?) !} }) {! !} {! !})
    φ' .Action.pres· g₀ g₁ = equivEq (funExt₂ {! !})

    φ* : Action G ΠHSet
    φ* .Action.action g = equivΠ (σ.action g) (η g)
    φ* .Action.pres· g₀ g₁ = equivEq (funExt₂ λ h x → {! !})


    Wreathᴰ : Group _
    Wreathᴰ .fst = ⟨ G ⟩ × (∀ x → ⟨ H x ⟩)
    Wreathᴰ .snd .GroupStr.1g = G.1g , H.1g
    Wreathᴰ .snd .GroupStr._·_ (g₀ , h₀) (g₁ , h₁) = g₀ G.· g₁ , λ x → {! !}
    Wreathᴰ .snd .GroupStr.inv = {! !}
    Wreathᴰ .snd .GroupStr.isGroup = {! !}

  {-
  private
    ΠA : Group _
    ΠA = ΠGroup {X = ⟨ Ω ⟩} (const A)

    ΠASet : hSet _
    ΠASet .fst = ⟨ ΠA ⟩
    ΠASet .snd = str ΠA .GroupStr.is-set

    module H = GroupStr (str H)
    module φ where
      open Action φ public
      open ActionProperties φ public


    φ* : Action H ΠASet
    φ* .Action.action h = equivΠDomain (invEquiv (φ.action h))
    φ* .Action.pres· h h′ = equivEq (funExt₂ goal) where
      φ⁻ : ⟨ H ⟩ → ⟨ Ω ⟩ → ⟨ Ω ⟩
      φ⁻ = invEq ∘ φ.action

      goal : (as : ⟨ Ω ⟩ → ⟨ A ⟩) (ω : ⟨ Ω ⟩) → as (φ⁻ (h H.· h′) ω) ≡ as (φ⁻ h (φ⁻ h′ ω))
      goal as ω = cong as $
        (φ⁻ (h H.· h′) ω) ≡⟨ φ.action-inv-comp h h′ ≡$ ω ⟩
        (φ⁻ h (φ⁻ h′ ω)) ∎

  Wreath : Group (ℓ-max (ℓ-max ℓΩ ℓA) ℓH)
  Wreath = ΠA ⋊[ φ* ] H
  -}

{- Op
module Op {ℓX ℓH ℓG} (X : hSet ℓX) (H : Group ℓH) (G : Group ℓG) (σ : Action G X) where
  private
    Gᵒᵖ = G ᵒᵖ

    ΠH : Group _
    ΠH = ΠGroup {X = ⟨ X ⟩} (const H)

    ΠHSet : hSet _
    ΠHSet .fst = ⟨ ΠH ⟩
    ΠHSet .snd = str ΠH .GroupStr.is-set

    module G = GroupStr (str G)
    module Gᵒᵖ = GroupStr (str Gᵒᵖ)

    module H = GroupStr (str H)
    module σ where
      open Action σ public
      open ActionProperties σ public

    σ* : Action Gᵒᵖ ΠHSet
    σ* .Action.action g = equivΠDomain (σ.action g)
    σ* .Action.pres· g g′ = equivEq (funExt₂ goal) where
      goal : (h : ⟨ X ⟩ → ⟨ H ⟩) (x : ⟨ X ⟩) → h ((g′ G.· g) σ.▷ x) ≡ h (g σ.▷ (g′ σ.▷ x))
      goal h x = cong h $ σ.action-comp-ext g′ g x

  Wreath : Group (ℓ-max (ℓ-max ℓX ℓH) ℓG)
  Wreath = ΠH ⋊[ σ* ] Gᵒᵖ

  module _ {ℓ} {Y : hSet ℓ} (τ : Action H Y) where
    private
      module τ where
        open Action τ public
        open ActionProperties τ public

    imprimitiveAction' : Action Wreath (X ×Set Y)
    imprimitiveAction' .Action.action (h , g) = Σ-cong-equiv (invEquiv $ σ.action g) λ x → τ.action (h (g σ.▷⁻ x))
    imprimitiveAction' .Action.pres· (h₀ , g₀) (h₁ , g₁) = equivEq $ funExt λ where
      (x , y) → ΣPathP λ where
        .fst → σ.action-inv-comp-ext g₁ g₀ x
        .snd →
          (h₀ ((g₁ G.· g₀) σ.▷⁻ x) H.· h₁ (g₀ σ.▷ ((g₁ G.· g₀) σ.▷⁻ x))) τ.▷ y
            ≡⟨ {! !} ⟩
          (h₀ ((g₁ G.· g₀) σ.▷⁻ x) H.· h₁ (g₀ σ.▷ (g₁ σ.▷⁻ (g₀ σ.▷⁻ x)))) τ.▷ y
            ≡⟨ {! !} ⟩
          (h₁ (g₁ σ.▷⁻ (g₀ σ.▷⁻ x)) τ.▷ (h₀ (g₀ σ.▷⁻ x) τ.▷ y))
            ∎

    imprimitiveAction : Action Wreath (X ×Set Y)
    imprimitiveAction .Action.action (hs , g) = Σ-cong-equiv (σ.action g) λ x → τ.action (hs (g σ.▷ x))
    -- imprimitiveAction' .Action.action (hs , g) .fst (x , y) = g σ.▷ x , (hs x τ.▷ y)
    -- imprimitiveAction' .Action.action (hs , g) .snd = {! !}
    imprimitiveAction .Action.pres· (hs₀ , g₀) (hs₁ , g₁) = equivEq $ funExt λ where
      (x , y) → ΣPathP λ where
        .fst → {! !} -- σ.action-comp-ext g₀ g₁ x
        .snd → {! !}
          -- (hs₀ ((g₀ G.· g₁) σ.▷ x) H.· hs₁ (g₀ σ.▷⁻ ((g₀ G.· g₁) σ.▷ x))) τ.▷ y
          --   ≡⟨ {! !} ⟩
          -- (hs₁ (g₁ σ.▷ (g₀ σ.▷ x)) τ.▷ (hs₀ (g₀ σ.▷ x) τ.▷ y))
          --   ∎
-}

module _ {ℓX ℓH ℓG} (X : hSet ℓX) (H : Group ℓH) (G : Group ℓG) (σ : Action G X) where
  private
    ΠH : Group _
    ΠH = ΠGroup {X = ⟨ X ⟩} (const H)

    ΠHSet : hSet _
    ΠHSet .fst = ⟨ ΠH ⟩
    ΠHSet .snd = str ΠH .GroupStr.is-set

    module G = GroupStr (str G)
    module H = GroupStr (str H)
    module σ where
      open Action σ public
      open ActionProperties σ public

    σ* : GroupHom (G ᵒᵖ) (Aut ΠH)
    σ* .fst g .fst = equivΠDomain $ σ.action g
    σ* .fst g .snd = makeIsGroupHom λ g g′ → refl
    σ* .snd = makeIsGroupHom λ g g′ → GroupEquiv≡ $ equivEq $ funExt₂ λ where
      h x → cong h $ σ.action-comp-ext g′ g x

  Wreath : Group (ℓ-max (ℓ-max ℓX ℓH) ℓG)
  Wreath = ΠH ⋊[ σ* ] G

  module _ {ℓ} {Y : hSet ℓ} (τ : Action H Y) where
    private
      module τ where
        open Action τ public
        open ActionProperties τ public

    imprimitiveAction : Action Wreath (X ×Set Y)
    imprimitiveAction .Action.action (hs , g) = Σ-cong-equiv (σ.action g) λ x → τ.action (hs x)
    imprimitiveAction .Action.pres· (hs₀ , g₀) (hs₁ , g₁) = equivEq $ funExt λ where
      (x , y) → ΣPathP λ where
        .fst → σ.action-comp-ext g₀ g₁ x
        .snd → τ.action-comp-ext (hs₀ x) (hs₁ (g₀ σ.▷ x)) y

    isFaithfulImprimitiveAction : isFaithful σ → isFaithful τ → isFaithful imprimitiveAction
    isFaithfulImprimitiveAction is-faithful-σ is-faithful-τ = isEmbedding→isFaithful imprimitiveAction $ hasPropFibersOfImage→isEmbedding {! !} where
      fiber-equiv' : (g* : ⟨ G ⟩) (h* : ⟨ X ⟩ → ⟨ H ⟩) → fiber (imprimitiveAction .Action.action) (Σ-cong-equiv (σ.action g*) (λ x → τ.action (h* x))) ≃ {! !}
      fiber-equiv' g* h* =
        Σ[ (h , g) ∈ (⟨ X ⟩ → ⟨ H ⟩) × ⟨ G ⟩ ] Σ-cong-equiv (σ.action g) (λ x → τ.action (h x)) ≡ Σ-cong-equiv (σ.action g*) (λ x → τ.action (h* x))
          ≃⟨ {! !} ⟩
        Σ[ (h , g) ∈ (⟨ X ⟩ → ⟨ H ⟩) × ⟨ G ⟩ ] ((x : ⟨ X ⟩) → (y : ⟨ Y ⟩) → ((g σ.▷ x) ≡ (g* σ.▷ x)) × ((h x τ.▷ y) ≡ (h* x τ.▷ y)))
          ≃⟨ {! !} ⟩
        {! !}
          ≃∎

      fiber-equiv : (w : ⟨ X ⟩ × ⟨ Y ⟩ ≃ ⟨ X ⟩ × ⟨ Y ⟩) → fiber (imprimitiveAction .Action.action) w ≃ {! !}
      fiber-equiv w =
        Σ[ (h , g) ∈ (⟨ X ⟩ → ⟨ H ⟩) × ⟨ G ⟩ ] Σ-cong-equiv (σ.action g) (λ x → τ.action (h x)) ≡ w
          ≃⟨ {! !} ⟩
        Σ[ (h , g) ∈ (⟨ X ⟩ → ⟨ H ⟩) × ⟨ G ⟩ ] equivFun (Σ-cong-equiv (σ.action g) (λ x → τ.action (h x))) ≡ equivFun w
          ≃⟨ {! !} ⟩
        Σ[ (h , g) ∈ (⟨ X ⟩ → ⟨ H ⟩) × ⟨ G ⟩ ] (∀ z → equivFun (Σ-cong-equiv (σ.action g) (λ x → τ.action (h x))) z ≡ equivFun w z)
          ≃⟨ {! !} ⟩
        Σ[ (h , g) ∈ (⟨ X ⟩ → ⟨ H ⟩) × ⟨ G ⟩ ] ((x : ⟨ X ⟩) → (y : ⟨ Y ⟩) → ((g σ.▷ x) , (h x τ.▷ y)) ≡ equivFun w (x , y))
          ≃⟨ {! !} ⟩
        Σ[ (h , g) ∈ (⟨ X ⟩ → ⟨ H ⟩) × ⟨ G ⟩ ] ((x : ⟨ X ⟩) → (y : ⟨ Y ⟩) → ((g σ.▷ x) ≡ equivFun w (x , y) .fst) × ((h x τ.▷ y) ≡ equivFun w (x , y) .snd))
          ≃⟨ {! !} ⟩
        {! !}
          ≃∎

    nonEmpty→isFaithfulImprimitiveAction : isFaithful σ → isFaithful τ → ∥ ⟨ Y ⟩ ∥₁ → isFaithful imprimitiveAction
    nonEmpty→isFaithfulImprimitiveAction is-faithful-σ is-faithful-τ ∣y∣ {g = (h₀ , g₀)} {h = (h₁ , g₁)} imprim-eq = ΣPathP λ where
        .fst → funExt λ x → is-faithful-τ $ equivEq $ funExt λ y → lemma x y .snd
        .snd → is-faithful-σ $ equivEq $ funExt λ x → PT.rec (str X _ _) (λ y → lemma x y .fst) ∣y∣
      where
        lemma : ∀ x y → (g₀ σ.▷ x ≡ g₁ σ.▷ x) × ((h₀ x) τ.▷ y ≡ (h₁ x) τ.▷ y)
        lemma x y .fst i = equivFun (imprim-eq i) (x , y) .fst
        lemma x y .snd i = equivFun (imprim-eq i) (x , y) .snd

    isTrivial→isFaithfulImprimitiveAction : isFaithful σ → isContr ⟨ H ⟩ → isFaithful imprimitiveAction
    isTrivial→isFaithfulImprimitiveAction is-faithful-σ is-triv-H {g = (h₀ , g₀)} {h = (h₁ , g₁)} htpy = ΣPathP λ where
        .fst → funExt λ x → isContr→isProp is-triv-H (h₀ x) (h₁ x)
        .snd → is-faithful-σ $ equivEq $ funExt λ x → {! cong equivFun htpy' ≡$ (x , ?) !}
      where
        htpy' : Σ-cong-equiv-fst {B = λ _ → ⟨ Y ⟩} (σ.action g₀) ≡ Σ-cong-equiv-fst (σ.action g₁)
        htpy' = {! !}

        fiber-equiv : (f : ⟨ X ⟩ × ⟨ Y ⟩ ≃ ⟨ X ⟩ × ⟨ Y ⟩) → fiber Σ-cong-equiv-fst f ≃ {! !}
        fiber-equiv f =
          Σ[ e ∈ ⟨ X ⟩ ≃ ⟨ X ⟩ ] Σ-cong-equiv-fst e ≡ f
            ≃⟨ {! !} ⟩
          Σ[ e ∈ ⟨ X ⟩ ≃ ⟨ X ⟩ ] equivFun (Σ-cong-equiv-fst e) ≡ equivFun f
            ≃⟨ {! !} ⟩
          Σ[ e ∈ ⟨ X ⟩ ≃ ⟨ X ⟩ ] (∀ z → equivFun (Σ-cong-equiv-fst e) z ≡ equivFun f z)
            ≃⟨ {! !} ⟩
          Σ[ e ∈ ⟨ X ⟩ ≃ ⟨ X ⟩ ] (∀ z → Σ[ p ∈ equivFun e (z .fst) ≡ (equivFun f z .fst) ] PathP (λ i → ⟨ Y ⟩) (z .snd) (equivFun f z .snd))
            ≃⟨ {! !} ⟩
          {! !}
            ≃∎

    isEmpty→isFaithfulImprimitiveAction : isFaithful σ → isFaithful τ → ¬ ⟨ Y ⟩ → isFaithful imprimitiveAction
    isEmpty→isFaithfulImprimitiveAction is-faithful-σ is-faithful-τ is-empty-Y {g = (h₀ , g₀)} {h = (h₁ , g₁)} htpy = {! !}

{-
module _ {ℓ}
  {Ω₀ Ω₁ : hSet ℓ}
  (ω : ⟨ Ω₀ ⟩ ≃ ⟨ Ω₁ ⟩)
  {A₀ A₁ : Group ℓ}
  (α : GroupEquiv A₀ A₁)
  {H₀ H₁ : Group ℓ}
  {φ₀ : Action H₀ Ω₀}
  {φ₁ : Action H₁ Ω₁}
  (η : GroupEquiv H₀ H₁)
  where
  private
    module α = IsGroupHom (α .snd)
    module φ₀ = Action φ₀

    ΠA-equiv : GroupEquiv (ΠGroup {X = ⟨ Ω₀ ⟩} $ const A₀) (ΠGroup {X = ⟨ Ω₁ ⟩} $ const A₁)
    ΠA-equiv .fst = equiv→ ω (α .fst)
    ΠA-equiv .snd .IsGroupHom.pres· _ _ = funExt λ _ → α.pres· _ _
    ΠA-equiv .snd .IsGroupHom.pres1 = funExt λ _ → α.pres1
    ΠA-equiv .snd .IsGroupHom.presinv _ = funExt λ _ → α.presinv _

  WreathEquiv :
    (∀ h → (φ₀ ⁻ h) ∘ invEq ω ≡ (invEq ω) ∘ (φ₁ ⁻ equivFun (η .fst) h))
    → GroupEquiv (Wreath Ω₀ A₀ H₀ φ₀) (Wreath Ω₁ A₁ H₁ φ₁)
  WreathEquiv comm = SemidirectProductEquiv _ _ ΠA-equiv η equivariant where
    equivariant : (a : ⟨ Ω₀ ⟩ → ⟨ A₀ ⟩) (h : ⟨ H₀ ⟩)
      → equivFun (α .fst) ∘ a ∘ (φ₀ ⁻ h) ∘ invEq ω ≡
        equivFun (α .fst) ∘ a ∘ (invEq ω) ∘ (φ₁ ⁻ equivFun (η .fst) h)
    equivariant a h = cong (λ - → equivFun (α .fst) ∘ a ∘ -) (comm h)

-}

private
  variable
    ℓ : Level
    A G H : Group ℓ
    Ω Ω′ : hSet ℓ
    σ : Action H Ω

isSubgroupTop : (ι : G ≤ H) → (Wreath Ω A G (GroupHomPreCompAction (ι .isSubgroup.inc) σ)) ≤ (Wreath Ω A H σ)
isSubgroupTop {G} {H} {Ω} {A} {σ} ι = Embedding→isSubgroup Σι $ makeIsGroupHom λ (α₀ , g₀) (α₁ , g₁) → ΣPathP (refl , ι.pres· g₀ g₁) where
  module ι = isSubgroup ι

  Σι : ((⟨ Ω ⟩ → ⟨ A ⟩) × ⟨ G ⟩) ↪ ((⟨ Ω ⟩ → ⟨ A ⟩) × ⟨ H ⟩)
  Σι = Σ-embed-snd λ _ → ι.inc-emb

isSubgroupTop' : (ι : G ≤ H) → (Wreath Ω′ A G {! !}) ≤ (Wreath Ω A H σ)
isSubgroupTop' = {! !}
