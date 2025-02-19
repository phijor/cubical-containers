open import GpdCont.Prelude

module GpdCont.ActionContainer.Mu (ℓ : Level) where

open import GpdCont.W
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Family.Base using (Fam)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.TwoCategory using (GroupAction)
open import GpdCont.Group.DirProd using (DirProd)
open import GpdCont.Group.SymmetricGroup using (𝔖)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Maybe
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)

module _ {ℓIx ℓo ℓh ℓr} (Ix : Type ℓIx) (C : TwoCategory ℓo ℓh ℓr) where
  private module C = TwoCategory C
  Copy : TwoCategory (ℓ-max ℓIx ℓo) (ℓ-max ℓIx ℓh) (ℓ-max ℓIx ℓr)
  Copy .TwoCategory.ob = Ix → C.ob
  Copy .TwoCategory.hom x y = (ix : Ix) → C.hom (x ix) (y ix)
  Copy .TwoCategory.rel f g = (ix : Ix) → C.rel (f ix) (g ix)
  Copy .TwoCategory.two-category-structure .TwoCategoryStr.id-hom x ix = C.id-hom (x ix)
  Copy .TwoCategory.two-category-structure .TwoCategoryStr.comp-hom f g ix = C.comp-hom (f ix) (g ix)
  Copy .TwoCategory.two-category-structure .TwoCategoryStr.id-rel f ix = C.id-rel (f ix)
  Copy .TwoCategory.two-category-structure .TwoCategoryStr.trans r s ix = C.trans (r ix) (s ix)
  Copy .TwoCategory.two-category-structure .TwoCategoryStr.comp-rel r s ix = C.comp-rel (r ix) (s ix)
  Copy .TwoCategory.is-two-category .IsTwoCategory.is-set-rel f g = isSetΠ λ ix → C.is-set-rel (f ix) (g ix)
  Copy .TwoCategory.is-two-category .IsTwoCategory.trans-assoc = {! !}
  Copy .TwoCategory.is-two-category .IsTwoCategory.trans-unit-left = {! !}
  Copy .TwoCategory.is-two-category .IsTwoCategory.trans-unit-right = {! !}
  Copy .TwoCategory.is-two-category .IsTwoCategory.comp-rel-id = {! !}
  Copy .TwoCategory.is-two-category .IsTwoCategory.comp-rel-trans = {! !}
  Copy .TwoCategory.is-two-category .IsTwoCategory.comp-hom-assoc = {! !}
  Copy .TwoCategory.is-two-category .IsTwoCategory.comp-hom-unit-left = {! !}
  Copy .TwoCategory.is-two-category .IsTwoCategory.comp-hom-unit-right = {! !}
  Copy .TwoCategory.is-two-category .IsTwoCategory.comp-rel-assoc = {! !}
  Copy .TwoCategory.is-two-category .IsTwoCategory.comp-rel-unit-left = {! !}
  Copy .TwoCategory.is-two-category .IsTwoCategory.comp-rel-unit-right = {! !}

module _ {ℓIx} (Ix : Type ℓIx) where
  ActCont : TwoCategory (ℓ-max (ℓ-suc ℓ) ℓIx) (ℓ-max ℓ ℓIx) (ℓ-max ℓ ℓIx)
  ActCont = Fam (Copy Ix (GroupAction ℓ)) ℓ

  module ActCont = TwoCategory ActCont

module ActCont₀ {ℓIx} {Ix : Type ℓIx} (F : ActCont.ob Ix) where
  Shape : hSet _
  Shape = F .fst

  Symm : Ix → ⟨ Shape ⟩ → Group ℓ
  Symm ix s = F .snd s ix .fst

  Pos : Ix → ⟨ Shape ⟩ → hSet ℓ
  Pos ix s = F .snd s ix .snd .fst

  action : (ix : Ix) → (s : ⟨ Shape ⟩) → Action (Symm ix s) (Pos ix s)
  action ix s = F .snd s ix .snd .snd

module _ {ℓIx} (Ix : Type ℓIx) where
  ActCont[_+1] : Type _
  ActCont[_+1] = ActCont.ob (Maybe Ix)

module ActCont+1₀ {ℓIx} {Ix : Type ℓIx} (F : ActCont[ Ix +1]) where
  open ActCont₀ F public

  Free : ⟨ Shape ⟩ → hSet _
  Free = Pos nothing

  Param : Ix → ⟨ Shape ⟩ → hSet _
  Param = Pos ∘ just

module _ {ℓIx} (Ix : Type ℓIx) (F : ActCont[ Ix +1]) where
  private module F = ActCont+1₀ F

  μShape : hSet ℓ
  μShape = W[ 1 ∣ s ∈ F.Shape ] ⟨ F.Free s ⟩

  μPos : ⟨ μShape ⟩ → Ix → hSet ℓ
  μPos w ix .fst = WFixᴰ (⟨_⟩ ∘ F.Param ix) w
  μPos w ix .snd = isOfHLevelFixᴰ _ 2 (str ∘ F.Param ix)

  μSymm : ⟨ μShape ⟩ → Ix → Group ℓ
  μSymm (sup-W s ws) ix = DirProd (F.Symm (just ix) s) (ΠGroup {X = ⟨ F.Free s ⟩} λ pos → μSymm (ws pos) ix)

  μSymm' : ⟨ μShape ⟩ → Ix → Group ℓ
  μSymm' (sup-W s ws) ix =
    DirProd
      (F.Symm (just ix) s) $
      DirProd
        (F.Symm nothing s)
        (ΠGroup {X = ⟨ F.Free s ⟩} λ pos → μSymm (ws pos) ix)

  μAction : (ix : Ix) → (w : ⟨ μShape ⟩) → Action (μSymm w ix) (μPos w ix)
  μAction ix = WIndExplicit goal where
    module _
      (s : ⟨ F.Shape ⟩) (ws : ⟨ F.Free s ⟩ → ⟨ μShape ⟩)
      (μ : ∀ free → Action (μSymm (ws free) ix) (μPos (ws free) ix))
      where
      w = sup-W s ws
      module μ {free : ⟨ F.Free s ⟩} = Action (μ free)

      σ : Action _ _
      σ = F.action (just ix) s

      module σ = Action σ

      ω-fun : ⟨ F.Symm (just ix) s ⟩ → ((free : ⟨ F.Free s ⟩) → ⟨ μSymm (ws free) ix ⟩) → ⟨ μPos w ix ⟩ → ⟨ μPos w ix ⟩
      ω-fun g fs (here param) = here $ the ⟨ F.Param ix s ⟩ (g σ.▷ param)
      ω-fun g fs (there free path) = there free (fs free μ.▷ path)

      ω-inv : ⟨ F.Symm (just ix) s ⟩ → ((free : ⟨ F.Free s ⟩) → ⟨ μSymm (ws free) ix ⟩) → ⟨ μPos w ix ⟩ → ⟨ μPos w ix ⟩
      ω-inv g fs (here param) = here (invEq (σ.action g) param)
      ω-inv g fs (there free path) = there free (invEq (μ.action (fs free)) path)

      is-equiv-ω : ∀ g fs → isEquiv (ω-fun g fs)
      is-equiv-ω g fs = isoToIsEquiv λ where
        .Iso.fun → ω-fun g fs
        .Iso.inv → ω-inv g fs
        .Iso.rightInv (here param) → cong here (secEq (σ.action g) param)
        .Iso.rightInv (there free path) → cong (there free) (secEq (μ.action (fs free)) path)
        .Iso.leftInv (here param) → cong here (retEq (σ.action g) param)
        .Iso.leftInv (there free path) → cong (there free) (retEq (μ.action (fs free)) path)

      ω : ⟨ F.Symm (just ix) s ⟩ × ((free : ⟨ F.Free s ⟩) → ⟨ μSymm (ws free) ix ⟩) → ⟨ μPos w ix ⟩ ≃ ⟨ μPos w ix ⟩
      ω (g , fs) .fst = ω-fun g fs
      ω (g , fs) .snd = is-equiv-ω g fs

      goal : Action _ _
      goal .Action.action = ω
      goal .Action.pres· (g , fs) (g′ , fs′) = equivEq $ funExt λ where
        (here param) → cong here $ cong equivFun (σ.pres· g g′) ≡$ param
        (there free path) → cong (there free) $ cong equivFun (μ.pres· (fs free) (fs′ free)) ≡$ path

  μAction' : (ix : Ix) → (w : ⟨ μShape ⟩) → Action (μSymm' w ix) (μPos w ix)
  μAction' ix = WIndExplicit goal where
    module _
      (s : ⟨ F.Shape ⟩) (ws : ⟨ F.Free s ⟩ → ⟨ μShape ⟩)
      (μ : ∀ free → Action (μSymm' (ws free) ix) (μPos (ws free) ix))
      where
      w = sup-W s ws
      module μ {free : ⟨ F.Free s ⟩} = Action (μ free)

      σ : Action _ _
      σ = F.action (just ix) s

      module σ = Action σ

      τ : Action _ _
      τ = F.action nothing s

      module τ = Action τ

      ω-fun : ⟨ F.Symm (just ix) s ⟩ → ⟨ F.Symm nothing s ⟩ → ((free : ⟨ F.Free s ⟩) → ⟨ μSymm' (ws free) ix ⟩) → ⟨ μPos w ix ⟩ → ⟨ μPos w ix ⟩
      ω-fun g h fs (here param) = here $ the ⟨ F.Param ix s ⟩ (g σ.▷ param)
      ω-fun g h fs (there free path) = there (h τ.▷ free) {! fs free μ.▷ _ !}

      goal : Action _ _
      goal .Action.action = {! !}
      goal .Action.pres· = {! !}

  μ : ActCont.ob Ix
  μ .fst = μShape
  μ .snd w ix .fst = μSymm w ix
  μ .snd w ix .snd .fst = μPos w ix
  μ .snd w ix .snd .snd = μAction ix w
