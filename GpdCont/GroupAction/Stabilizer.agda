module GpdCont.GroupAction.Stabilizer where
open import GpdCont.Prelude hiding (_▷_)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Faithful
open import GpdCont.Group.Subgroup
open import GpdCont.Group.Equivs using (conjEquiv ; conjHom)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Foundations.Powerset as ℙ using (ℙ)
open import Cubical.Functions.Logic using (_⇔_ ; ⇔-id ; ⊓-comm)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath using (GroupPath)

module Stabilizer {ℓG ℓX}
  (G : Group ℓG)
  (X : hSet ℓX)
  (σ : Action G X)
  where

  private
    open module G = GroupStr (str G) using (_·_)

    module σ where
      open Action σ public
      open ActionProperties σ public

    open σ using (_▷_)

  module _ (x : ⟨ X ⟩) where
    isStabilizer : ⟨ G ⟩ → Type _
    isStabilizer g = (g ▷ x) ≡ x

    isPropIsStabilizer : ∀ g → isProp (isStabilizer g)
    isPropIsStabilizer g = str X _ _

    opaque
      isStabilizer-1g : isStabilizer G.1g
      isStabilizer-1g = σ.action-1-id ≡$ x

      isStabilizer-· : ∀ {g h} → isStabilizer g → isStabilizer h → isStabilizer (g · h)
      isStabilizer-· {g} {h} gx≡x hx≡x =
        (g · h) ▷ x ≡⟨ σ.action-comp g h ≡$ x ⟩
        h ▷ (g ▷ x) ≡⟨ cong (h ▷_) gx≡x ⟩
        h ▷ x ≡⟨ hx≡x ⟩
        x ∎

      isStabilizer-inv : ∀ {g} → isStabilizer g → isStabilizer (G.inv g)
      isStabilizer-inv {g} gx≡x =
        G.inv g ▷ x ≡⟨ σ.action-inv g ≡$ x ⟩
        (σ ⁻ g) x ≡⟨ σ.action-inv-adj g gx≡x ⟩
        x ∎

    Stabilizer≡ : {g h : Σ ⟨ G ⟩ isStabilizer} → g .fst ≡ h .fst → g ≡ h
    Stabilizer≡ = Σ≡Prop isPropIsStabilizer

    StabilizerGroup : Group _
    StabilizerGroup .fst = Σ[ g ∈ ⟨ G ⟩ ] isStabilizer g
    StabilizerGroup .snd .GroupStr.1g .fst = G.1g
    StabilizerGroup .snd .GroupStr.1g .snd = isStabilizer-1g
    StabilizerGroup .snd .GroupStr._·_ (g , gx≡x) (h , hx≡x) .fst = g · h
    StabilizerGroup .snd .GroupStr._·_ (g , gx≡x) (h , hx≡x) .snd = isStabilizer-· gx≡x hx≡x
    StabilizerGroup .snd .GroupStr.inv (g , gx≡x) .fst = G.inv g
    StabilizerGroup .snd .GroupStr.inv (g , gx≡x) .snd = isStabilizer-inv gx≡x
    StabilizerGroup .snd .GroupStr.isGroup = makeIsGroup (isSetΣSndProp G.is-set isPropIsStabilizer)
      {! !}
      {! !}
      {! !}
      {! !}
      {! !}

    stabilizerInclusion : GroupHom StabilizerGroup G
    stabilizerInclusion .fst = fst
    stabilizerInclusion .snd .IsGroupHom.pres· _ _ = refl
    stabilizerInclusion .snd .IsGroupHom.pres1 = refl
    stabilizerInclusion .snd .IsGroupHom.presinv _ = refl

    isContrKerStabilizerInclusion : isContrKer stabilizerInclusion
    isContrKerStabilizerInclusion = isInjective→isContrKer stabilizerInclusion λ { (g , _) g≡1 → Stabilizer≡ g≡1 }

    StabilizerSubgroup : Subgroup G (ℓ-max ℓG ℓX)
    StabilizerSubgroup .Subgroup.sub = StabilizerGroup
    StabilizerSubgroup .Subgroup.is-sub .isSubgroup.inc = stabilizerInclusion
    StabilizerSubgroup .Subgroup.is-sub .isSubgroup.is-contr-ker-inc = isContrKerStabilizerInclusion

module Setwise {ℓG ℓX} (G : Group ℓG) (X : hSet ℓX) (σ : Action G X) where
  open import GpdCont.GroupAction.Powerset

  private
    ℙσ = PowersetAction G X σ
    open module G = GroupStr (str G) using (_·_)
    module σ where
      open Action σ public
      open ActionProperties σ public

    ℙ→Σ : ℙ ⟨ X ⟩ → hSet _
    ℙ→Σ S .fst = Σ ⟨ X ⟩ (⟨_⟩ ∘ S)
    ℙ→Σ S .snd = isSetΣSndProp (str X) (str ∘ S)

  open Stabilizer G _ ℙσ public

  module _ (S : ℙ ⟨ X ⟩) where
    isStabilizer' : ⟨ G ⟩ → Type _
    isStabilizer' g = ∀ x → ⟨ S (g σ.▷ x) ⇔ S x ⟩

    isPropIsStabilizer' : ∀ g → isProp (isStabilizer' g)
    isPropIsStabilizer' g = isPropΠ λ x → str (S (g σ.▷ x) ⇔ S x)

    stab-act : ∀ g → isStabilizer' g → ∀ x → ⟨ S x ⟩ ≃ ⟨ S (g σ.▷ x) ⟩
    stab-act g p x = propBiimpl→Equiv (str (S x)) (str (S (g σ.▷ x)))
      (p x .snd)
      (p x .fst)

    StabilizerSubroup' : Subgroup G (ℓ-max ℓG ℓX)
    StabilizerSubroup' = isClosedSubset→Subgroup G isStabilizer' isPropIsStabilizer'
      (λ { x → subst (λ - → ⟨ S - ⇔ S x ⟩) (sym (σ.action-1-id ≡$ x)) (⇔-id (S x)) })
      {! !}
      λ { {g} stab-g x → let (p , q) = (stab-g (G.inv g σ.▷ x)) in subst (λ - → ⟨ S (G.inv g σ.▷ x) ⇔ S - ⟩) {! σ.action-inv !} (q , p) }

    StabilizerGroup' : Group (ℓ-max ℓG ℓX)
    StabilizerGroup' = Subgroup.sub StabilizerSubroup'

    SubsetAction' : Action StabilizerGroup' (ℙ→Σ S)
    SubsetAction' .Action.action (g , p) = Σ-cong-equiv (σ.action g) (stab-act g p)
    SubsetAction' .Action.pres· (g , p) (h , q) = equivEq $ funExt λ (x , _) → Σ≡Prop (str ∘ S) $ σ.action-comp g h ≡$ x

    isFaithfulSubsetAction' : isFaithful σ → isFaithful SubsetAction'
    isFaithfulSubsetAction' is-faithful-σ {g = g , p} {h = h , q} Σ-cong-equiv-path = Σ≡Prop isPropIsStabilizer' goal where
      goal : g ≡ h
      goal = is-faithful-σ $ equivEq $ funExt λ x → cong fst $ cong equivFun Σ-cong-equiv-path ≡$ (x , {!q x!})

  SetwiseStabilizerSubgroup : (S : ℙ ⟨ X ⟩) → Subgroup G (ℓ-max ℓG (ℓ-suc ℓX))
  SetwiseStabilizerSubgroup = StabilizerSubgroup

  SubsetAction : (S : ℙ ⟨ X ⟩) → Action (StabilizerGroup S) (ℙ→Σ S)
  SubsetAction S .Action.action (g , p) = Σ-cong-equiv (σ.action g) λ x → pathToEquiv $
    let p-ext = S ≡[ i ]⟨ S ∘ (λ x → retEq (σ.action g) x (~ i)) ⟩
                S ∘ (σ ⁻ g) ∘ (σ ⁺ g) ≡[ i ]⟨ S ∘ σ.action-inv g (~ i) ∘ (σ ⁺ g) ⟩
                S ∘ (σ ⁺ G.inv g) ∘ (σ ⁺ g) ≡[ i ]⟨ p i ∘ (σ ⁺ g) ⟩
                (S ∘ σ ⁺ g) ∎
    in cong ⟨_⟩ $ p-ext ≡$ x
  SubsetAction S .Action.pres· (g , p) (h , q) = equivEq $ funExt λ (x , _) → Σ≡Prop (str ∘ S) $ σ.action-comp g h ≡$ x

  module _ (S R : ℙ ⟨ X ⟩) (g₀ : ⟨ G ⟩) (p : S ≡ R ∘ (σ ⁺ g₀)) where
    private
      p⁻ : S ∘ (σ ⁻ g₀) ≡ R
      p⁻ = sym $ σ.precomp-inv g₀ p

      {- AAARRHHAHAAAHHHHHHH -}
      to : ∀ g → (S ∘ (σ ⁺ G.inv g) ≡ S) → (R ∘ (σ ⁺ G.inv (G.inv g₀ · g · g₀)) ≡ R)
      to g q =
        R ∘ (σ ⁺ G.inv (G.inv g₀ · g · g₀))
          ≡⟨ cong (R ∘_) (σ.action-inv _) ⟩
        R ∘ (σ ⁻ (G.inv g₀ · g · g₀))
          ≡⟨ cong (R ∘_) $ σ.action-inv-comp (G.inv g₀) _ ∙ cong (σ ⁻ G.inv g₀ ∘_) (σ.action-inv-comp g g₀) ⟩
        R ∘ σ ⁻ (G.inv g₀) ∘ σ ⁻ g ∘ σ ⁻ g₀
          ≡[ i ]⟨ R ∘ σ.action-inv-inv g₀ i ∘ σ ⁻ g ∘ σ ⁻ g₀ ⟩
        (R ∘ σ ⁺ g₀) ∘ σ ⁻ g ∘ σ ⁻ g₀
          ≡[ i ]⟨ p (~ i) ∘ σ ⁻ g ∘ σ ⁻ g₀ ⟩
        S ∘ σ ⁻ g ∘ σ ⁻ g₀
          ≡[ i ]⟨ S ∘ σ.action-inv g (~ i) ∘ σ ⁻ g₀ ⟩
        S ∘ σ ⁺ (G.inv g) ∘ σ ⁻ g₀
          ≡[ i ]⟨ q i ∘ σ ⁻ g₀ ⟩
        S ∘ σ ⁻ g₀
          ≡⟨ p⁻ ⟩
        R ∎

      from : ∀ g → R ∘ (σ ⁺ G.inv (G.inv g₀ · g · g₀)) ≡ R → S ∘ (σ ⁺ G.inv g) ≡ S
      from g q = sym $
        S
          ≡⟨ p ⟩
        R ∘ (σ ⁺ g₀)
          ≡[ i ]⟨ q (~ i) ∘ (σ ⁺ g₀) ⟩
        R ∘ (σ ⁺ G.inv (G.inv g₀ · g · g₀)) ∘ (σ ⁺ g₀)
          ≡[ i ]⟨ R ∘ shuffle i ⟩
        R ∘ σ ⁻ (G.inv g₀) ∘ (σ ⁻ g)
          ≡[ i ]⟨ p⁻ (~ i) ∘ σ ⁻ (G.inv g₀) ∘ (σ ⁻ g) ⟩
        S ∘ σ ⁻ g₀ ∘ σ ⁻ (G.inv g₀) ∘ (σ ⁻ g)
          ≡[ i ]⟨ S ∘ σ ⁻ g₀ ∘ σ.action-inv-inv g₀ i ∘ (σ ⁻ g) ⟩
        S ∘ σ ⁻ g₀ ∘ σ ⁺ g₀ ∘ (σ ⁻ g)
          ≡[ i ]⟨ S ∘ σ.action-cancel-right' g₀ i ∘ (σ ⁻ g) ⟩
        S ∘ (σ ⁻ g)
          ≡[ i ]⟨ S ∘ σ.action-inv g (~ i) ⟩
        S ∘ (σ ⁺ G.inv g)
          ∎
        where
          shuffle : _ ≡ _
          shuffle =
            (σ ⁺ G.inv (G.inv g₀ · g · g₀)) ∘ (σ ⁺ g₀)
              ≡[ i ]⟨ σ.action-inv (G.inv g₀ · g · g₀) i ∘ (σ ⁺ g₀) ⟩
            (σ ⁻ (G.inv g₀ · g · g₀)) ∘ (σ ⁺ g₀)
              ≡⟨ cong (_∘ (σ ⁺ g₀)) $ σ.action-inv-comp₂ (G.inv g₀) g g₀ ⟩
            σ ⁻ (G.inv g₀) ∘ (σ ⁻ g) ∘ (σ ⁻ g₀) ∘ (σ ⁺ g₀)
              ≡[ i ]⟨ σ ⁻ (G.inv g₀) ∘ (σ ⁻ g) ∘ σ.action-cancel-right' g₀ i ⟩
            σ ⁻ (G.inv g₀) ∘ (σ ⁻ g)
              ∎

      equivᴰ : ∀ g → (S ∘ (σ ⁺ G.inv g) ≡ S) ≃ (R ∘ (σ ⁺ G.inv (G.inv g₀ · g · g₀)) ≡ R)
      equivᴰ g = propBiimpl→Equiv (isOfHLevelPath' 1 ℙ.isSetℙ _ _) (isOfHLevelPath' 1 ℙ.isSetℙ _ _)
        (to g)
        (from g)

    equiv : (Σ[ g ∈ ⟨ G ⟩ ] S ∘ (σ ⁺ G.inv g) ≡ S) ≃ (Σ[ g ∈ ⟨ G ⟩ ] R ∘ (σ ⁺ G.inv g) ≡ R)
    equiv = Σ-cong-equiv (conjEquiv G g₀) equivᴰ

    opaque
      equiv-hom : IsGroupHom (str $ StabilizerGroup S) (equivFun equiv) (str $ StabilizerGroup R)
      equiv-hom = makeIsGroupHom λ where
        (g , p) (h , q) → ΣPathP (conjHom G g₀ .snd .IsGroupHom.pres· g h , {! !})

    equivSubset→GroupEquiv : GroupEquiv (StabilizerGroup S) (StabilizerGroup R)
    equivSubset→GroupEquiv .fst = equiv
    equivSubset→GroupEquiv .snd = equiv-hom

    private
      to' : ∀ {g} → isStabilizer' S g → isStabilizer' R (G.inv g₀ · g · g₀)
      to' {g} stab-g x .fst r = subst ⟨_⟩ ({- cong S (σ.action-inv g₀ ≡$ x) ∙ -} (p⁻ ≡$ x)) $ the ⟨ S (g₀ σ.▷⁻ x) ⟩ $
        stab-g _ .fst {!r!}
      to' {g} stab-g x .snd = {! !}

      equiv'ᴰ : ∀ g → isStabilizer' S g ≃ isStabilizer' R (G.inv g₀ · g · g₀)
      equiv'ᴰ g = propBiimpl→Equiv (isPropIsStabilizer' S _) (isPropIsStabilizer' R _)
        to'
        {! !}

    equivSubset→GroupEquiv' : GroupEquiv (StabilizerGroup' S) (StabilizerGroup' R)
    equivSubset→GroupEquiv' .fst = Σ-cong-equiv (conjEquiv G g₀) equiv'ᴰ
    equivSubset→GroupEquiv' .snd = {! !}

    equivSubset→GroupPath : StabilizerGroup S ≡ StabilizerGroup R
    equivSubset→GroupPath = equivFun (GroupPath _ _) equivSubset→GroupEquiv

    equivSubset→SetwiseStabilizerSubgroupPath :
      SubgroupPath (SetwiseStabilizerSubgroup S) (SetwiseStabilizerSubgroup R)
    equivSubset→SetwiseStabilizerSubgroupPath .fst = equivSubset→GroupEquiv
    equivSubset→SetwiseStabilizerSubgroupPath .snd = {! !}

open Stabilizer public
