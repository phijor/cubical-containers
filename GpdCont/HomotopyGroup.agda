open import GpdCont.Prelude

module GpdCont.HomotopyGroup (ℓ : Level) where

open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Subcategory using (Subcategory ; ForgetLax)
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.Displayed.Base
open import GpdCont.TwoCategory.Displayed.LocallyThin as LT using (IsLocallyThinOver ; LocallyThinOver)
open import GpdCont.TwoCategory.HomotopyGroupoid renaming (hGpdCat to hGroupoid)
open import GpdCont.Connectivity using (isPathConnected ; isPropIsPathConnected)

open import Cubical.Foundations.Equiv.Base using (fiber)
open import Cubical.Foundations.HLevels hiding (hGroupoid)
open import Cubical.Foundations.Isomorphism using (section)
open import Cubical.Foundations.Path as Path using (compPath→Square)
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

isLocallyThinOverPointedStr : IsLocallyThinOver (hGroupoid ℓ) _ _ _ Pointed₀ Pointed₁ Pointed₂ PointedStr
isLocallyThinOverPointedStr .IsLocallyThinOver.is-prop-relᴰ {y = H} φ₀ ψ₀ = isGroupoid→isPropSquare (str H)
isLocallyThinOverPointedStr .IsLocallyThinOver.comp-hom-assocᴰ = {! !}
isLocallyThinOverPointedStr .IsLocallyThinOver.comp-hom-unit-leftᴰ = {! !}
isLocallyThinOverPointedStr .IsLocallyThinOver.comp-hom-unit-rightᴰ = {! !}

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

ForgetPointed : LaxFunctor Pointed (hGroupoid ℓ)
ForgetPointed = TotalTwoCategory.Fst (hGroupoid ℓ) _

private
  module Pointed = TwoCategory Pointed

isPointedConnectedGroupoid : Pointed.ob → hProp _
isPointedConnectedGroupoid (G , G⋆) = isPathConnected ⟨ G ⟩ , isPropIsPathConnected _

hGroup : TwoCategory (ℓ-suc ℓ) ℓ ℓ
hGroup = Subcategory Pointed isPointedConnectedGroupoid

ForgetConnected : LaxFunctor hGroup Pointed
ForgetConnected = ForgetLax Pointed isPointedConnectedGroupoid

ForgetGroup : LaxFunctor hGroup (hGroupoid ℓ)
ForgetGroup = compLaxFunctor ForgetConnected ForgetPointed
