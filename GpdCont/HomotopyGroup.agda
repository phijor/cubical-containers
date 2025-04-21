open import GpdCont.Prelude

module GpdCont.HomotopyGroup (ℓ : Level) where

open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Subcategory using (Subcategory ; Forget)
open import GpdCont.TwoCategory.StrictFunctor
open import GpdCont.TwoCategory.Displayed.Base
open import GpdCont.TwoCategory.Displayed.LocallyThin as LT using (IsLocallyThinOver ; LocallyThinOver)
open import GpdCont.TwoCategory.HomotopyGroupoid renaming (hGpdCat to hGroupoid)
import      GpdCont.Univalence as Univalence
open import GpdCont.Connectivity using (isPathConnected ; isPropIsPathConnected)

open import Cubical.Foundations.Equiv.Base using (fiber ; equivFun)
open import Cubical.Foundations.HLevels hiding (hGroupoid)
open import Cubical.Foundations.Isomorphism using (section)
open import Cubical.Foundations.Path as Path using (compPath→Square)
import      Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Data.Sigma using (Σ≡Prop ; ΣPathP)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

private
  module hGroupoid = TwoCategory (hGroupoid ℓ)

Pointed₀ : hGroupoid.ob → Type ℓ
Pointed₀ G = ⟨ G ⟩
{-# INJECTIVE_FOR_INFERENCE Pointed₀ #-}

Pointed₁[_,_] : (G H : hGroupoid.ob) (φ : hGroupoid.hom G H) → (g₀ : Pointed₀ G) → (h₀ : Pointed₀ H) → Type ℓ
Pointed₁[_,_] _ _ φ g₀ h₀ = φ g₀ ≡ h₀
{-# INJECTIVE_FOR_INFERENCE Pointed₁[_,_] #-}

Pointed₁ : {G H : hGroupoid.ob}
  → (φ : hGroupoid.hom G H) → (g₀ : Pointed₀ G) → (h₀ : Pointed₀ H) → Type ℓ
Pointed₁ {G} {H} = Pointed₁[ G , H ]
{-# INJECTIVE_FOR_INFERENCE Pointed₁ #-}

Pointed₂[_,_] : ∀ (G H : hGroupoid.ob) {φ ψ : hGroupoid.hom G H}
  → {g₀ : Pointed₀ G}
  → {h₀ : Pointed₀ H}
  → (r : hGroupoid.rel {G} {H} φ ψ)
  → (φ₀ : Pointed₁[ G , H ] φ g₀ h₀)
  → (ψ₀ : Pointed₁[ G , H ] ψ g₀ h₀)
  → Type ℓ
Pointed₂[_,_] _ _ {g₀} {h₀} r φ₀ ψ₀ = PathP (λ i → r i g₀ ≡ h₀) φ₀ ψ₀
{-# INJECTIVE_FOR_INFERENCE Pointed₂[_,_] #-}

Pointed₂ : ∀ {G H : hGroupoid.ob} {φ ψ : hGroupoid.hom G H}
  → {g₀ : Pointed₀ G}
  → {h₀ : Pointed₀ H}
  → (r : hGroupoid.rel {G} {H} φ ψ)
  → (φ₀ : Pointed₁[ G , H ] φ g₀ h₀)
  → (ψ₀ : Pointed₁[ G , H ] ψ g₀ h₀)
  → Type ℓ
Pointed₂ {G} {H} = Pointed₂[ G , H ]
{-# INJECTIVE_FOR_INFERENCE Pointed₂ #-}

pt-id₁ : ∀ {G} (g₀ : Pointed₀ G) → Pointed₁[ G , G ] (id ⟨ G ⟩) g₀ g₀
pt-id₁ g₀ = refl′ g₀

pt-comp₁ : ∀ {G H K} {φ : hGroupoid.hom G H} {ψ : hGroupoid.hom H K}
  → {g₀ : Pointed₀ G}
  → {h₀ : Pointed₀ H}
  → {k₀ : Pointed₀ K}
  → Pointed₁ φ g₀ h₀
  → Pointed₁ ψ h₀ k₀
  → Pointed₁ (φ hGroupoid.∙₁ ψ) g₀ k₀
pt-comp₁ {ψ} φ₀ ψ₀ = cong ψ φ₀ ∙ ψ₀

pt-id₂ : ∀ {G H} {φ : hGroupoid.hom G H} {g₀ : Pointed₀ G} {h₀ : Pointed₀ H}
  → (φ₀ : Pointed₁ φ g₀ h₀) → Pointed₂ (hGroupoid.id-rel φ) φ₀ φ₀
pt-id₂ φ₀ = refl′ φ₀

pt-trans : ∀ {G H} {φ ψ ρ : hGroupoid.hom G H}
  → {r : hGroupoid.rel φ ψ}
  → {s : hGroupoid.rel ψ ρ}
  → {g₀ : Pointed₀ G} {h₀ : Pointed₀ H}
  → {φ₀ : Pointed₁ φ g₀ h₀}
  → {ψ₀ : Pointed₁ ψ g₀ h₀}
  → {ρ₀ : Pointed₁ ρ g₀ h₀}
  → Pointed₂ r φ₀ ψ₀
  → Pointed₂ s ψ₀ ρ₀
  → Pointed₂ (r ∙ s) φ₀ ρ₀
pt-trans {r} {s} r₀ s₀ = compPathP' {B = λ γ → Pointed₁ γ _ _} {p = r} {q = s} r₀ s₀

pt-comp₂ : ∀ {G H K}
  → {φ₁ φ₂ : hGroupoid.hom G H} {ψ₁ ψ₂ : hGroupoid.hom H K}
  → {r : hGroupoid.rel φ₁ φ₂} {s : hGroupoid.rel ψ₁ ψ₂}
  → {g₀ : Pointed₀ G} {h₀ : Pointed₀ H} {k₀ : Pointed₀ K}
  → {φ₁⋆ : Pointed₁ φ₁ g₀ h₀} {φ₂⋆ : Pointed₁ φ₂ g₀ h₀}
  → {ψ₁⋆ : Pointed₁ ψ₁ h₀ k₀} {ψ₂⋆ : Pointed₁ ψ₂ h₀ k₀}
  → Pointed₂ r φ₁⋆ φ₂⋆
  → Pointed₂ s ψ₁⋆ ψ₂⋆
  → Pointed₂ (r hGroupoid.∙ₕ s) (pt-comp₁ {φ = φ₁} {ψ = ψ₁} φ₁⋆ ψ₁⋆) (pt-comp₁ {φ = φ₂} {ψ = ψ₂} φ₂⋆ ψ₂⋆)
pt-comp₂ {φ₁} {φ₂} {ψ₁} {ψ₂} {r} {s} {g₀} {h₀} {k₀} {φ₁⋆} {φ₂⋆} {ψ₁⋆} {ψ₂⋆} r₀ s₀ = goal where
  🪞 = Path.flipSquare

  r₀′ : PathP (λ i → s i (r i g₀) ≡ s i h₀) (λ i → ψ₁ (φ₁⋆ i)) (λ i → ψ₂ (φ₂⋆ i))
  r₀′ i j = s i (r₀ i j)

  goal : Square (pt-comp₁ {φ = φ₁} {ψ = ψ₁} φ₁⋆ ψ₁⋆) (pt-comp₁ {φ = φ₂} {ψ = ψ₂} φ₂⋆ ψ₂⋆) ((r hGroupoid.∙ₕ s) ≡$ g₀) (refl′ k₀)
  goal = 🪞 (🪞 r₀′ Path.∙v' 🪞 s₀)

PointedStr : TwoCategoryStrᴰ (hGroupoid ℓ) _ _ _ Pointed₀ Pointed₁ Pointed₂
PointedStr .TwoCategoryStrᴰ.id-homᴰ = pt-id₁
PointedStr .TwoCategoryStrᴰ.comp-homᴰ = pt-comp₁
PointedStr .TwoCategoryStrᴰ.id-relᴰ = pt-id₂
PointedStr .TwoCategoryStrᴰ.transᴰ = pt-trans
PointedStr .TwoCategoryStrᴰ.comp-relᴰ = pt-comp₂

pt-comp-hom-assoc : ∀ {x y z w : hGroupoid.ob}
  → {f : hGroupoid.hom x y} {g : hGroupoid.hom y z} {h : hGroupoid.hom z w}
  → {xᴰ : Pointed₀ x} {yᴰ : Pointed₀ y} {zᴰ : Pointed₀ z} {wᴰ : Pointed₀ w}
  → (fᴰ : Pointed₁ f xᴰ yᴰ)
  → (gᴰ : Pointed₁ g yᴰ zᴰ)
  → (hᴰ : Pointed₁ h zᴰ wᴰ)
  → Path (Pointed₁ (h ∘ g ∘ f) xᴰ wᴰ)
    (cong h (cong g fᴰ ∙ gᴰ) ∙ hᴰ)
    (cong (h ∘ g) fᴰ ∙ (cong h gᴰ ∙ hᴰ))
pt-comp-hom-assoc {f} {g} {h} {xᴰ} {wᴰ} fᴰ gᴰ hᴰ =
  cong h (cong g fᴰ ∙ gᴰ) ∙ hᴰ          ≡⟨ cong (_∙ hᴰ) (GL.cong-∙ h (cong g fᴰ) gᴰ) ⟩
  (cong h (cong g fᴰ) ∙ cong h gᴰ) ∙ hᴰ ≡⟨ sym (GL.assoc (cong (h ∘ g) fᴰ) (cong h gᴰ) hᴰ) ⟩
  (cong (h ∘ g) fᴰ ∙ (cong h gᴰ ∙ hᴰ))  ∎

isLocallyThinOverPointedStr : IsLocallyThinOver (hGroupoid ℓ) _ _ _ Pointed₀ Pointed₁ Pointed₂ PointedStr
isLocallyThinOverPointedStr .IsLocallyThinOver.is-prop-relᴰ {y = H} φ₀ ψ₀ = isGroupoid→isPropSquare (str H)
isLocallyThinOverPointedStr .IsLocallyThinOver.comp-hom-assocᴰ = pt-comp-hom-assoc
isLocallyThinOverPointedStr .IsLocallyThinOver.comp-hom-unit-leftᴰ gᴰ = sym (GL.lUnit gᴰ)
isLocallyThinOverPointedStr .IsLocallyThinOver.comp-hom-unit-rightᴰ fᴰ = sym (GL.rUnit fᴰ)

Pointedᵀ : LocallyThinOver (hGroupoid ℓ) ℓ ℓ ℓ
Pointedᵀ .LocallyThinOver.ob[_] = Pointed₀
Pointedᵀ .LocallyThinOver.hom[_] {x = G} {y = H} = Pointed₁ {G} {H}
Pointedᵀ .LocallyThinOver.rel[_] {x = G} {y = H} = Pointed₂ {G} {H}
Pointedᵀ .LocallyThinOver.two-category-structureᴰ = PointedStr
Pointedᵀ .LocallyThinOver.is-locally-thinᴰ = isLocallyThinOverPointedStr

Pointedᴰ : TwoCategoryᴰ (hGroupoid ℓ) ℓ ℓ ℓ
Pointedᴰ = LocallyThinOver.toTwoCategoryᴰ Pointedᵀ

Pointed : TwoCategory (ℓ-suc ℓ) ℓ ℓ
Pointed = TotalTwoCategory.∫ (hGroupoid ℓ) Pointedᴰ

ForgetPointed : StrictFunctor Pointed (hGroupoid ℓ)
ForgetPointed = TotalTwoCategory.Fst (hGroupoid ℓ) _

private
  module Pointed = TwoCategory Pointed

isPointedConnectedGroupoid : Pointed.ob → hProp _
isPointedConnectedGroupoid (G , G⋆) = isPathConnected ⟨ G ⟩ , isPropIsPathConnected _

hGroup : TwoCategory (ℓ-suc ℓ) ℓ ℓ
hGroup = Subcategory Pointed isPointedConnectedGroupoid

module hGroup where
  open TwoCategory hGroup public

  ⌜_⌝ : ob → Type _
  ⌜ (((G , _) , _) , _) ⌝ = G
  {-# INJECTIVE_FOR_INFERENCE ⌜_⌝ #-}

  is-groupoid : (G : ob) → isGroupoid ⌜ G ⌝
  is-groupoid (((_ , p) , _) , _) = p

  is-connected : (G : ob) → isPathConnected ⌜ G ⌝
  is-connected = snd

  pt : (G : ob) → ⌜ G ⌝
  pt ((_ , ∙) , _) = ∙

  fun : ∀ {G H : ob} → hom G H → ⌜ G ⌝ → ⌜ H ⌝
  fun (φ , _) = φ
  {-# INJECTIVE_FOR_INFERENCE fun #-}

  ua : {G H : ob} → (e : ⌜ G ⌝ ≃ ⌜ H ⌝) → equivFun e (pt G) ≡ pt H → G ≡ H
  ua e p = Σ≡Prop (str ∘ isPointedConnectedGroupoid) (ΣPathP (TypeOfHLevel≡ 3 (Univalence.ua e) , Univalence.ua-gluePath e p))
  {-# INJECTIVE_FOR_INFERENCE ua #-}

ForgetConnected : StrictFunctor hGroup Pointed
ForgetConnected = Forget Pointed isPointedConnectedGroupoid

ForgetGroup : StrictFunctor hGroup (hGroupoid ℓ)
ForgetGroup = compStrictFunctor ForgetConnected ForgetPointed

module _ where
  open import Cubical.Categories.Category.Base

  postulate
    isSetHGroupHom : ∀ x y → isSet (hGroup.hom x y)
    isGroupoidHGroup : isGroupoid hGroup.ob
    

  hGroupStrict : Category (ℓ-suc ℓ) ℓ
  hGroupStrict .Category.ob = hGroup.ob
  hGroupStrict .Category.Hom[_,_] = hGroup.hom
  hGroupStrict .Category.id {x} = hGroup.id-hom x
  hGroupStrict .Category._⋆_ {x} {y} {z} = hGroup.comp-hom {x} {y} {z}
  hGroupStrict .Category.⋆IdL {x} {y} = hGroup.comp-hom-unit-left {x} {y}
  hGroupStrict .Category.⋆IdR {x} {y} = hGroup.comp-hom-unit-right {x} {y}
  hGroupStrict .Category.⋆Assoc {x} {y} {z} {w} = hGroup.comp-hom-assoc {x} {y} {z} {w}
  hGroupStrict .Category.isSetHom {x} {y} = isSetHGroupHom x y

  module hGroupStrict = Category hGroupStrict

module _ where
  open import Cubical.Categories.Category.Base
  open import Cubical.Categories.Functor.Base
  open import Cubical.Categories.Instances.Groups
  open import Cubical.Categories.NaturalTransformation.Base as NT using (_≅ᶜ_)
  open import Cubical.Categories.Equivalence.AdjointEquivalence
  open import Cubical.Algebra.Group.Base
  open import Cubical.Algebra.Group.Morphisms
  open import Cubical.Algebra.Group.MorphismProperties

  open import GpdCont.Group.FundamentalGroup using (π₁)
  import      GpdCont.Delooping as Delooping
  import      GpdCont.Delooping.Map as Map

  private
    module GroupCategory = Category (GroupCategory {ℓ})
    Ω₀ : hGroupStrict.ob → Group _
    Ω₀ ((X , x₀) , _) = π₁ X x₀

    Ω₁ : ∀ {X Y : hGroupStrict.ob}
      → hGroupStrict.Hom[ X , Y ]
      → GroupHom (Ω₀ X) (Ω₀ Y)
    Ω₁ (f , fx₀≡y₀) .fst p = (sym fx₀≡y₀) ∙∙ cong f p ∙∙ fx₀≡y₀
    Ω₁ (f , fx₀≡y₀) .snd .IsGroupHom.pres· = {! !}
    Ω₁ (f , fx₀≡y₀) .snd .IsGroupHom.pres1 = {! !}
    Ω₁ (f , fx₀≡y₀) .snd .IsGroupHom.presinv = {! !}

  Ω : Functor hGroupStrict (GroupCategory {ℓ})
  Ω .Functor.F-ob = Ω₀
  Ω .Functor.F-hom {x} {y} = Ω₁ {x} {y}
  Ω .Functor.F-id {x} = GroupHom≡ $ funExt λ p → sym (doubleCompPath-filler refl p refl)
  Ω .Functor.F-seq f g = {! !}

  private
    𝔹₀ : Group ℓ → hGroup.ob
    𝔹₀ G .fst .fst .fst = Delooping.𝔹 G
    𝔹₀ G .fst .fst .snd = Delooping.isGroupoid𝔹
    𝔹₀ G .fst .snd = Delooping.⋆
    𝔹₀ G .snd = Delooping.isConnectedDelooping G

    𝔹₁ : ∀ {G H : Group ℓ} → GroupHom G H → hGroup.hom (𝔹₀ G) (𝔹₀ H)
    𝔹₁ φ .fst = Map.map φ
    𝔹₁ φ .snd = refl

  𝔹 : Functor (GroupCategory {ℓ}) hGroupStrict
  𝔹 .Functor.F-ob = 𝔹₀
  𝔹 .Functor.F-hom = 𝔹₁
  𝔹 .Functor.F-id {x = G} i .fst = Map.map-id G i
  𝔹 .Functor.F-id {x = G} i .snd j = Delooping.⋆
  𝔹 .Functor.F-seq φ ψ i .fst = Map.map-comp φ ψ i
  𝔹 .Functor.F-seq φ ψ i .snd j = doubleCompPath-filler {x = Delooping.⋆} refl refl refl i j

  η₀ : (G : Group ℓ) → GroupHom G (Ω₀ (𝔹₀ G))
  η₀ G = Delooping.loopHom G

  η₁ : ∀ {G H : Group ℓ} → (φ : GroupHom G H) → φ GroupCategory.⋆ (η₀ H) ≡ η₀ G GroupCategory.⋆ (Ω₁ {X = 𝔹₀ G} {Y = 𝔹₀ H} (𝔹₁ φ))
  η₁ φ = GroupHom≡ λ i g → doubleCompPath-filler {x = (Map.map φ Delooping.⋆)} refl (cong (Map.map φ) (Delooping.loop g)) refl i

  isIso-η : ∀ G → isIso GroupCategory (η₀ G)
  isIso-η G .isIso.inv = Delooping.unloopGroupHom G
  isIso-η G .isIso.sec = GroupHom≡ $ funExt $ Delooping.encodeDecodeIso G .Iso.leftInv
  isIso-η G .isIso.ret = GroupHom≡ $ funExt $ Delooping.encodeDecodeIso G {y = Delooping.⋆} .Iso.rightInv

  η : 𝟙⟨ GroupCategory ⟩ ≅ᶜ Ω ∘F 𝔹
  η .NT.NatIso.trans .NT.NatTrans.N-ob = η₀
  η .NT.NatIso.trans .NT.NatTrans.N-hom {x} {y} φ = η₁ {x} {y} φ
  η .NT.NatIso.nIso = isIso-η

  ε₀ : (G : hGroup.ob) → hGroup.hom (𝔹₀ (Ω₀ G)) G
  ε₀ G .fst = Delooping.rec (Ω₀ G) (G .fst .fst .snd) (hGroup.pt G) (id _) pathComp→compSquareFiller
  ε₀ G .snd = refl

  ε : 𝔹 ∘F Ω ≅ᶜ 𝟙⟨ hGroupStrict ⟩
  ε .NT.NatIso.trans .NT.NatTrans.N-ob = ε₀
  ε .NT.NatIso.trans .NT.NatTrans.N-hom = {! !}
  ε .NT.NatIso.nIso = {! !}

  DeloopingEquiv : AdjointEquivalence (GroupCategory {ℓ}) hGroupStrict
  DeloopingEquiv .AdjointEquivalence.fun = 𝔹
  DeloopingEquiv .AdjointEquivalence.inv = Ω
  DeloopingEquiv .AdjointEquivalence.η = η
  DeloopingEquiv .AdjointEquivalence.ε = ε
  DeloopingEquiv .AdjointEquivalence.triangleIdentities = {! !}
