{-# OPTIONS --lossy-unification #-}
module GpdCont.GroupAction.Delooping where

open import GpdCont.Prelude
open import GpdCont.Univalence using (ua ; ua→)
open import GpdCont.Connectivity using (isPathConnected)

open import GpdCont.GroupAction.Base using (Action ; _⁺_ ; module ActionProperties)
open import GpdCont.GroupAction.Equivariant renaming (isEquivariantMap[_][_,_] to isEquivariantMap)
open import GpdCont.GroupAction.TwoCategory using (GroupActionᴰ ; GroupAction)
open import GpdCont.GroupAction.AssociatedBundle using (associatedBundle ; associatedBundleMap ; associatedBundleMapEquiv)
open import GpdCont.Group.TwoCategory using (TwoGroup)

open import GpdCont.SetBundle.Base using (SetBundle ; SetBundleᴰ ; SetBundleᵀ ; isLocallyGroupoidalSetBundle ; module SetBundleNotation)

import      GpdCont.Delooping as Delooping
open import GpdCont.Delooping.Functor using (module TwoFunc ; module LocalInverse)
import      GpdCont.Delooping.Map as DeloopingMap

open import GpdCont.TwoCategory.Base using (TwoCategory)
open import GpdCont.TwoCategory.LaxFunctor using (LaxFunctor)
open import GpdCont.TwoCategory.StrictFunctor using (StrictFunctor)
open import GpdCont.TwoCategory.Pseudofunctor using (isPseudoFunctor ; isLocallyGroupoidal→isPseudofunctor)
open import GpdCont.TwoCategory.LocalCategory using (LocalCategory)
open import GpdCont.TwoCategory.LocalFunctor as LocalFunctor using (isLocallyFullyFaithful ; isLocallyEssentiallySurjective ; isLocallyWeakEquivalence)
open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryᴰ)
open import GpdCont.TwoCategory.Displayed.LaxFunctor using (LaxFunctorᴰ)
open import GpdCont.TwoCategory.Displayed.StrictFunctor using (StrictFunctorᴰ)
open import GpdCont.TwoCategory.Displayed.LocallyThin using (IntoLocallyThin)
open import GpdCont.TwoCategory.HomotopyGroupoid using (hGpdCat)

open import Cubical.Foundations.Equiv as Equiv using (isEquiv ; equivFun ; equivIsEquiv ; fiber ; invEq ; _∙ₑ_)
open import Cubical.Foundations.HLevels using (isOfHLevelPathP' ; isSet→ ; isSet→SquareP)
open import Cubical.Foundations.Path using (compPath→Square)
open import Cubical.Foundations.Transport using (subst⁻ ; subst⁻-filler ; substCommSlice)
open import Cubical.Functions.FunExtEquiv using (funExtEquiv ; funExtDep)
import      Cubical.Data.Sigma as Sigma
open import Cubical.Algebra.Group.MorphismProperties using (GroupHom≡)

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

-- Delooping of group actions into set bundles as a functor of 2-categories.
-- =========================================================================
--
-- We define this functor by extending the delooping-functor of groups to
-- a lax functor on total 2-categories
--
--    𝔹 : ∫ Group GroupActionᴰ → ∫ hGpd SetBundleᴰ
--
-- In particular, we only need to give the "displayed" part of the functor,
-- and since its target has locally thin displayed 2-cells, it suffices to
-- give the following data:
--
--  ∙ 𝔹ᴰ₀, assigning to a group action its associated bundle,
--  ∙ 𝔹ᴰ₁, assigning to an equivariant map its associated map of bundles
--  ∙ 𝔹ᴰ₂, assigning to a conjugator of actions a homotopy of bundle maps
--
-- ...and proofs that 𝔹 (laxly) preserves identity 2-cells and vertical composites.
module _ (ℓ : Level) where
  private
    module Group = TwoCategory (TwoGroup ℓ)
    module GroupAction = TwoCategory (GroupAction ℓ)
    module GroupActionᴰ = TwoCategoryᴰ (GroupActionᴰ ℓ)
    module hGpdCat = TwoCategory (hGpdCat ℓ)

    module SetBundle = SetBundleNotation ℓ
    -- module SetBundleᴰ = TwoCategoryᴰ (SetBundleᴰ ℓ)

    open Delooping.𝔹 using (⋆ ; loop)
    𝔹 = TwoFunc.TwoDeloopingˢ ℓ
    module 𝔹 = StrictFunctor 𝔹

    𝔹-lax = TwoFunc.TwoDelooping ℓ
    module 𝔹-lax = LaxFunctor 𝔹-lax

    -- To each group action, assign its associated bundle:
    𝔹ᴰ₀ : ∀ {G} → GroupActionᴰ.ob[ G ] → SetBundle.ob[ 𝔹.₀ G ]
    𝔹ᴰ₀ (X , σ) = associatedBundle {X = X} σ
    -- {-# INJECTIVE_FOR_INFERENCE 𝔹ᴰ₀ #-}

  -- Any equivariant map of group actions is exactly a map of associated bundles.
  𝔹ᴰ₁-equiv : ∀ {G H} {φ : Group.hom G H} {Xᴳ : GroupActionᴰ.ob[ G ]} {Yᴴ : GroupActionᴰ.ob[ H ]}
    → GroupActionᴰ.hom[ φ ] Xᴳ Yᴴ ≃ SetBundle.hom[ 𝔹.₁ φ ] (𝔹ᴰ₀ Xᴳ) (𝔹ᴰ₀ Yᴴ)
  𝔹ᴰ₁-equiv {φ} {Xᴳ = _ , σ} {Yᴴ = _ , τ} = associatedBundleMapEquiv σ τ φ

  private
    𝔹ᴰ₁ : ∀ {G H} {φ : Group.hom G H} {Xᴳ : GroupActionᴰ.ob[ G ]} {Yᴴ : GroupActionᴰ.ob[ H ]}
      → GroupActionᴰ.hom[ φ ] Xᴳ Yᴴ
      → SetBundle.hom[ 𝔹.₁ φ ] (𝔹ᴰ₀ Xᴳ) (𝔹ᴰ₀ Yᴴ)
    𝔹ᴰ₁ = equivFun 𝔹ᴰ₁-equiv
    {-# INJECTIVE_FOR_INFERENCE 𝔹ᴰ₁ #-}

    𝔹ᴰ₁⁻¹ : ∀ {G H} {φ : Group.hom G H} {Xᴳ : GroupActionᴰ.ob[ G ]} {Yᴴ : GroupActionᴰ.ob[ H ]}
      → SetBundle.hom[ 𝔹.₁ φ ] (𝔹ᴰ₀ Xᴳ) (𝔹ᴰ₀ Yᴴ)
      → GroupActionᴰ.hom[ φ ] Xᴳ Yᴴ
    𝔹ᴰ₁⁻¹ = invEq 𝔹ᴰ₁-equiv

  isEquiv-𝔹ᴰ₁ : ∀ {G H} {φ : Group.hom G H} {Xᴳ : GroupActionᴰ.ob[ G ]} {Yᴴ : GroupActionᴰ.ob[ H ]}
    → isEquiv (𝔹ᴰ₁ {G} {H} {φ} {Xᴳ} {Yᴴ})
  isEquiv-𝔹ᴰ₁ = equivIsEquiv 𝔹ᴰ₁-equiv

  private
    -- Path lemma characterizing displayed homotopies of set bundle maps
    -- with a delooping in their codomain.  Such homotopies are defined
    -- pointwise in the delooping; and since the target is a proposition
    -- (SetBundleᴰ is locally thin), it suffices to give the homotopy on
    -- the point.
    module _
      {G} {Y} {f g : hGpdCat.hom (𝔹.₀ G) Y} {r : hGpdCat.rel f g}
      {Xᴳ : GroupActionᴰ.ob[ G ]}
      (yᴰ : SetBundle.ob[ Y ])
      {fᴰ : SetBundle.hom[ f ] (𝔹ᴰ₀ Xᴳ) yᴰ}
      {gᴰ : SetBundle.hom[ g ] (𝔹ᴰ₀ Xᴳ) yᴰ}
      where
      open Delooping G using (elimPropEquiv)
      opaque
        isProp𝔹ᴰ₁PathP : ∀ x → isProp (PathP (λ i → ⟨ yᴰ (r i x) ⟩ → ⟨ 𝔹ᴰ₀ Xᴳ x ⟩) (fᴰ x) (gᴰ x))
        isProp𝔹ᴰ₁PathP x = isOfHLevelPathP' 1 (isSet→ is-set-𝔹ᴰ₀) _ _ where
          is-set-𝔹ᴰ₀ : isSet ⟨ 𝔹ᴰ₀ Xᴳ x ⟩
          is-set-𝔹ᴰ₀ = str $ 𝔹ᴰ₀ Xᴳ x

        𝔹ᴰ₁-PathPEquiv :
          (PathP (λ i → ⟨ yᴰ (r i ⋆) ⟩ → ⟨ 𝔹ᴰ₀ Xᴳ ⋆ ⟩) (fᴰ ⋆) (gᴰ ⋆))
            ≃
          (∀ x → PathP (λ i → ⟨ yᴰ (r i x) ⟩ → ⟨ 𝔹ᴰ₀ Xᴳ x ⟩) (fᴰ x) (gᴰ x))
        𝔹ᴰ₁-PathPEquiv = elimPropEquiv isProp𝔹ᴰ₁PathP

        𝔹ᴰ₁-PathP≃SetBundleRel : (PathP (λ i → ⟨ yᴰ (r i ⋆) ⟩ → ⟨ 𝔹ᴰ₀ Xᴳ ⋆ ⟩) (fᴰ ⋆) (gᴰ ⋆)) ≃ (SetBundle.rel[_] {yᴰ = yᴰ} r fᴰ gᴰ)
        𝔹ᴰ₁-PathP≃SetBundleRel = 𝔹ᴰ₁-PathPEquiv ∙ₑ funExtEquiv
        {-# INJECTIVE_FOR_INFERENCE 𝔹ᴰ₁-PathP≃SetBundleRel #-}

        𝔹ᴰ₁PathP : (p⋆ : PathP (λ i → ⟨ yᴰ (r i ⋆) ⟩ → ⟨ 𝔹ᴰ₀ Xᴳ ⋆ ⟩) (fᴰ ⋆) (gᴰ ⋆))
          → SetBundle.rel[_] {yᴰ = yᴰ} r fᴰ gᴰ
        𝔹ᴰ₁PathP = equivFun 𝔹ᴰ₁-PathP≃SetBundleRel

  -- A conjugator relating two equivariant maps is exactly a homotopy of associated bundle maps.
  -- We define the map underlying this equivalence to be the action of 𝔹 on 2-cells.
  module _
    {G H} {φ ψ : Group.hom G H}
    {r : Group.rel φ ψ}
    {Xᴳ : GroupActionᴰ.ob[ G ]}
    {Yᴴ @ (Y , τ) : GroupActionᴰ.ob[ H ]}
    {fᴰ @ (f , _) : GroupActionᴰ.hom[ φ ] Xᴳ Yᴴ}
    {gᴰ @ (g , _) : GroupActionᴰ.hom[ ψ ] Xᴳ Yᴴ}
    where

    -- Some `r` is a conjugator of `f` and `g` iff and only if it identifies it identifies
    -- them as a permutation of their domain.
    𝔹ᴰ₂-equiv : (GroupActionᴰ.rel[ r ] fᴰ gᴰ) ≃ (SetBundle.rel[_] {yᴰ = 𝔹ᴰ₀ Yᴴ} (𝔹.₂ {f = φ} {g = ψ} r) (𝔹ᴰ₁ fᴰ) (𝔹ᴰ₁ gᴰ))
    𝔹ᴰ₂-equiv =
      (GroupActionᴰ.rel[ r ] fᴰ gᴰ) ≃⟨ ActionProperties.uaExtEquiv τ {f₀ = f} {f₁ = g} (r .fst) ⟩
      (PathP (λ i → ⟨ 𝔹ᴰ₀ {H} Yᴴ (𝔹.₂ {f = φ} {g = ψ} r i ⋆) ⟩ → ⟨ 𝔹ᴰ₀ {G} Xᴳ ⋆ ⟩) f g) ≃⟨ 𝔹ᴰ₁-PathP≃SetBundleRel {f = 𝔹.₁ φ} {g = 𝔹.₁ ψ} {r = 𝔹.₂ r} (𝔹ᴰ₀ Yᴴ) ⟩
      (SetBundle.rel[_] {yᴰ = 𝔹ᴰ₀ Yᴴ} (𝔹.₂ r) (𝔹ᴰ₁ fᴰ) (𝔹ᴰ₁ gᴰ)) ≃∎

    𝔹ᴰ₂ : GroupActionᴰ.rel[ r ] fᴰ gᴰ → SetBundle.rel[_] {yᴰ = 𝔹ᴰ₀ Yᴴ} (𝔹.₂ {f = φ} {g = ψ} r) (𝔹ᴰ₁ fᴰ) (𝔹ᴰ₁ gᴰ)
    𝔹ᴰ₂ = equivFun 𝔹ᴰ₂-equiv
    {-# INJECTIVE_FOR_INFERENCE 𝔹ᴰ₂ #-}

    isEquiv-𝔹ᴰ₂ : isEquiv 𝔹ᴰ₂
    isEquiv-𝔹ᴰ₂ = equivIsEquiv 𝔹ᴰ₂-equiv

  private
    𝔹-rel-id : ∀ {x y : Group.ob} {f : Group.hom x y} {xᴰ : GroupActionᴰ.ob[ x ]} {yᴰ : GroupActionᴰ.ob[ y ]}
      → (fᴰ : GroupActionᴰ.hom[ f ] xᴰ yᴰ)
      → PathP (λ i → SetBundle.rel[_] {yᴰ = 𝔹ᴰ₀ yᴰ} (𝔹.F-rel-id {f = f} i) (𝔹ᴰ₁ fᴰ) (𝔹ᴰ₁ fᴰ))
          (𝔹ᴰ₂ {r = Group.id-rel f} (GroupActionᴰ.id-relᴰ fᴰ))
          (SetBundle.id-relᴰ {yᴰ = 𝔹ᴰ₀ yᴰ} (𝔹ᴰ₁ fᴰ))
    𝔹-rel-id {f} {yᴰ} fᴰ = SetBundle.relᴰ≡ {yᴰ = 𝔹ᴰ₀ yᴰ} (𝔹.F-rel-id {f = f})

    𝔹-rel-trans : ∀ {x y} {f g h : Group.hom x y} {r : Group.rel f g} {s : Group.rel g h}
      → {xᴰ : GroupActionᴰ.ob[ x ]} {yᴰ : GroupActionᴰ.ob[ y ]}
      → {fᴰ : GroupActionᴰ.hom[ f ] xᴰ yᴰ}
      → {gᴰ : GroupActionᴰ.hom[ g ] xᴰ yᴰ}
      → {hᴰ : GroupActionᴰ.hom[ h ] xᴰ yᴰ}
      → (rᴰ : GroupActionᴰ.rel[ r ] fᴰ gᴰ)
      → (sᴰ : GroupActionᴰ.rel[ s ] gᴰ hᴰ)
      → PathP (λ i → SetBundle.rel[_] {yᴰ = 𝔹ᴰ₀ yᴰ} (𝔹.F-rel-trans r s i) (𝔹ᴰ₁ fᴰ) (𝔹ᴰ₁ hᴰ))
          (𝔹ᴰ₂ (GroupActionᴰ.transᴰ {r = r} {s = s} {fᴰ = fᴰ} {gᴰ = gᴰ} {hᴰ = hᴰ} rᴰ sᴰ))
          (SetBundle.transᴰ {yᴰ = 𝔹ᴰ₀ yᴰ} {gᴰ = 𝔹ᴰ₁ gᴰ} (𝔹ᴰ₂ rᴰ) (𝔹ᴰ₂ sᴰ))
    𝔹-rel-trans {r} {s} {yᴰ} rᴰ sᴰ = SetBundle.relᴰ≡ {r = 𝔹.₂ (r Group.∙ᵥ s)} {s = 𝔹.₂ r hGpdCat.∙ᵥ 𝔹.₂ s} {yᴰ = 𝔹ᴰ₀ yᴰ} (𝔹.F-rel-trans r s)

    𝔹-hom-comp : ∀ {x y z} {f : Group.hom x y} {g : Group.hom y z}
      → {xᴰ : GroupActionᴰ.ob[ x ]} {yᴰ : GroupActionᴰ.ob[ y ]} {zᴰ : GroupActionᴰ.ob[ z ]}
      → (fᴰ : GroupActionᴰ.hom[ f ] xᴰ yᴰ) (gᴰ : GroupActionᴰ.hom[ g ] yᴰ zᴰ)
      → PathP (λ i → SetBundle.hom[ 𝔹.F-hom-comp f g i ] (𝔹ᴰ₀ xᴰ) (𝔹ᴰ₀ zᴰ))
        (SetBundle.comp-homᴰ {f = 𝔹.₁ f} {g = 𝔹.₁ g} {zᴰ = 𝔹ᴰ₀ zᴰ} (𝔹ᴰ₁ fᴰ) (𝔹ᴰ₁ gᴰ))
        (𝔹ᴰ₁ (fᴰ GroupActionᴰ.∙₁ᴰ gᴰ))
    𝔹-hom-comp {x = G} {z = K} {f} {g} {xᴰ} {zᴰ} fᴰ gᴰ = 𝔹ᴰ₁PathP (𝔹ᴰ₀ zᴰ) refl

    𝔹-hom-id : ∀ {x} (xᴰ : GroupActionᴰ.ob[ x ])
      → PathP (λ i → SetBundle.hom[ 𝔹.F-hom-id x i ] (𝔹ᴰ₀ xᴰ) (𝔹ᴰ₀ xᴰ))
        (SetBundle.id-homᴰ (𝔹ᴰ₀ xᴰ))
        (𝔹ᴰ₁ (GroupActionᴰ.id-homᴰ xᴰ))
    𝔹-hom-id {x} xᴰ = 𝔹ᴰ₁PathP (𝔹ᴰ₀ xᴰ) refl

  private
    -- On the point, 𝔹 stricly preserves vertical composition of 2-cells...
    𝔹-trans-lax : ∀ {G H K} {φ : Group.hom G H} {ψ : Group.hom H K}
      → {Xᴳ : GroupActionᴰ.ob[ G ]}
      → {Yᴴ : GroupActionᴰ.ob[ H ]}
      → {Zᴷ : GroupActionᴰ.ob[ K ]}
      → (fᴰ : GroupActionᴰ.hom[ φ ] Xᴳ Yᴴ)
      → (gᴰ : GroupActionᴰ.hom[ ψ ] Yᴴ Zᴷ)
      → SetBundle.rel[_] {yᴰ = 𝔹ᴰ₀ Zᴷ} (𝔹-lax.F-trans-lax φ ψ) (SetBundle.comp-homᴰ {zᴰ = 𝔹ᴰ₀ Zᴷ} (𝔹ᴰ₁ fᴰ) (𝔹ᴰ₁ gᴰ)) (𝔹ᴰ₁ (fᴰ GroupActionᴰ.∙₁ᴰ gᴰ))
    𝔹-trans-lax {Zᴷ} (f , _) (g , _) = 𝔹ᴰ₁PathP (𝔹ᴰ₀ Zᴷ) $ refl′ (f ∘ g)

    -- ...and similarly for identity 2-cells:
    𝔹-id-lax : ∀ {G}
      → (Xᴳ : GroupActionᴰ.ob[ G ])
      → SetBundle.rel[_] (𝔹-lax.F-id-lax G) (SetBundle.id-homᴰ (𝔹ᴰ₀ Xᴳ)) (𝔹ᴰ₁ (GroupActionᴰ.id-homᴰ Xᴳ))
    𝔹-id-lax = 𝔹-hom-id

  -- The above data assembles into a lax functor (𝔹 : GroupAction → SetBundle).
  𝔹ᵀ : IntoLocallyThin 𝔹-lax (GroupActionᴰ ℓ) (SetBundleᵀ ℓ)
  𝔹ᵀ .IntoLocallyThin.F-obᴰ = 𝔹ᴰ₀
  𝔹ᵀ .IntoLocallyThin.F-homᴰ = 𝔹ᴰ₁
  𝔹ᵀ .IntoLocallyThin.F-relᴰ = 𝔹ᴰ₂
  𝔹ᵀ .IntoLocallyThin.F-trans-laxᴰ = 𝔹-trans-lax
  𝔹ᵀ .IntoLocallyThin.F-id-laxᴰ = 𝔹-id-lax

  𝔹ᴰ : LaxFunctorᴰ 𝔹-lax (GroupActionᴰ ℓ) (SetBundleᴰ ℓ)
  𝔹ᴰ = IntoLocallyThin.toLaxFunctorᴰ 𝔹ᵀ

  Delooping : LaxFunctor (GroupAction ℓ) (SetBundle ℓ)
  Delooping = LaxFunctorᴰ.toTotalFunctor 𝔹ᴰ

  𝔹ᴰˢ : StrictFunctorᴰ 𝔹 (GroupActionᴰ ℓ) (SetBundleᴰ ℓ)
  𝔹ᴰˢ .StrictFunctorᴰ.F-obᴰ = 𝔹ᴰ₀
  𝔹ᴰˢ .StrictFunctorᴰ.F-homᴰ = 𝔹ᴰ₁
  𝔹ᴰˢ .StrictFunctorᴰ.F-relᴰ = 𝔹ᴰ₂
  𝔹ᴰˢ .StrictFunctorᴰ.F-rel-idᴰ = 𝔹-rel-id
  𝔹ᴰˢ .StrictFunctorᴰ.F-rel-transᴰ = 𝔹-rel-trans
  𝔹ᴰˢ .StrictFunctorᴰ.F-hom-compᴰ = 𝔹-hom-comp
  𝔹ᴰˢ .StrictFunctorᴰ.F-hom-idᴰ = 𝔹-hom-id
  𝔹ᴰˢ .StrictFunctorᴰ.F-assoc-filler-leftᴰ fᴰ gᴰ hᴰ = doubleCompPathP→DoubleCompPathPFiller _ _ _ _
  𝔹ᴰˢ .StrictFunctorᴰ.F-assoc-filler-rightᴰ fᴰ gᴰ hᴰ = doubleCompPathP→DoubleCompPathPFiller _ _ _ _
  𝔹ᴰˢ .StrictFunctorᴰ.F-assocᴰ {f} {g} {h} {xᴰ} {wᴰ} fᴰ gᴰ hᴰ = isSet→SquareP (λ i j → SetBundle.isSetHomᴰ (𝔹.F-assoc f g h i j) (𝔹ᴰ₀ xᴰ) (𝔹ᴰ₀ wᴰ)) _ _ _ _
  𝔹ᴰˢ .StrictFunctorᴰ.F-unit-left-fillerᴰ fᴰ = doubleCompPathP→DoubleCompPathPFiller _ _ _ _
  𝔹ᴰˢ .StrictFunctorᴰ.F-unit-leftᴰ {f} {xᴰ} {yᴰ} fᴰ = isSet→SquareP (λ i j → SetBundle.isSetHomᴰ (𝔹.F-unit-left f i j) (𝔹ᴰ₀ xᴰ) (𝔹ᴰ₀ yᴰ)) _ _ _ _
  𝔹ᴰˢ .StrictFunctorᴰ.F-unit-right-fillerᴰ fᴰ = doubleCompPathP→DoubleCompPathPFiller _ _ _ _
  𝔹ᴰˢ .StrictFunctorᴰ.F-unit-rightᴰ {f} {xᴰ} {yᴰ} fᴰ = isSet→SquareP (λ i j → SetBundle.isSetHomᴰ (𝔹.F-unit-right f i j) (𝔹ᴰ₀ xᴰ) (𝔹ᴰ₀ yᴰ)) _ _ _ _

  Deloopingˢ : StrictFunctor (GroupAction ℓ) (SetBundle ℓ)
  Deloopingˢ = StrictFunctorᴰ.toTotalFunctor 𝔹ᴰˢ

  private
    module ∫𝔹ᴰ = StrictFunctor Deloopingˢ

  isPseudoFunctorDelooping : isPseudoFunctor Delooping
  isPseudoFunctorDelooping = isLocallyGroupoidal→isPseudofunctor Delooping (isLocallyGroupoidalSetBundle ℓ)

  private
    module 𝔹Act where
      open LaxFunctor Delooping public
      open LocalFunctor Delooping public

  isConnectedDeloopingBase : (σ : GroupAction.ob) → isPathConnected ⟨ SetBundle.Base (∫𝔹ᴰ.₀ σ) ⟩
  isConnectedDeloopingBase (G , (X , σ)) = Delooping.isConnectedDelooping G

  isLocallyFullyFaithfulDelooping : 𝔹Act.isLocallyFullyFaithful
  isLocallyFullyFaithfulDelooping σ τ f@(φ , _) g@(ψ , _) = goal where
    ∫𝔹₁ = LaxFunctor.F-hom Delooping

    ∫𝔹₂ : GroupAction.rel f g → SetBundle.rel (∫𝔹₁ f) (∫𝔹₁ g)
    ∫𝔹₂ = LaxFunctor.F-rel Delooping {f = f} {g = g}

    ∫𝔹₂-equiv : GroupAction.rel f g ≃ SetBundle.rel (∫𝔹₁ f) (∫𝔹₁ g)
    ∫𝔹₂-equiv = Sigma.Σ-cong-equiv
      (TwoFunc.localDeloopingEmbedding ℓ φ ψ)
       λ (r : Group.rel φ ψ) → 𝔹ᴰ₂-equiv {r = r}

    goal : isEquiv ∫𝔹₂
    goal = equivIsEquiv ∫𝔹₂-equiv

  module _
    {G H : Group.ob}
    (Xᴳ @ (X , σ) : GroupActionᴰ.ob[ G ])
    (Yᴴ @ (Y , τ) : GroupActionᴰ.ob[ H ])
    (f : hGpdCat.hom (𝔹.₀ G) (𝔹.₀ H))
    (fᴰ : SetBundle.hom[ f ] (𝔹ᴰ₀ Xᴳ) (𝔹ᴰ₀ Yᴴ))
    (φ : Group.hom G H)
    (φ-sec : 𝔹.₁ φ ≡ f)
    where
    𝔹ᴰ₁-sectionOver : Σ[ φᴰ ∈ GroupActionᴰ.hom[ φ ] Xᴳ Yᴴ ] PathP (λ i → SetBundle.hom[ φ-sec i ] (𝔹ᴰ₀ Xᴳ) (𝔹ᴰ₀ Yᴴ)) (𝔹ᴰ₁ φᴰ) fᴰ
    𝔹ᴰ₁-sectionOver = goal where
      fᴰ′ : SetBundle.hom[ 𝔹.₁ φ ] (𝔹ᴰ₀ Xᴳ) (𝔹ᴰ₀ Yᴴ)
      fᴰ′ = subst (λ φ → SetBundle.hom[ φ ] (𝔹ᴰ₀ Xᴳ) (𝔹ᴰ₀ Yᴴ)) (sym φ-sec) fᴰ

      fᴰ′-filler : PathP (λ i → SetBundle.hom[ φ-sec (~ i) ] (𝔹ᴰ₀ Xᴳ) (𝔹ᴰ₀ Yᴴ)) fᴰ fᴰ′
      fᴰ′-filler = subst-filler (λ φ → SetBundle.hom[ φ ] (𝔹ᴰ₀ Xᴳ) (𝔹ᴰ₀ Yᴴ)) (sym φ-sec) fᴰ

      φᴰ : GroupActionᴰ.hom[ φ ] Xᴳ Yᴴ
      φᴰ = 𝔹ᴰ₁⁻¹ fᴰ′

      φᴰ-sec : fᴰ′ ≡ 𝔹ᴰ₁ φᴰ
      φᴰ-sec = sym (Equiv.secEq (𝔹ᴰ₁-equiv {Xᴳ = Xᴳ} {Yᴴ = Yᴴ}) fᴰ′)

      goal : Σ _ _
      goal .fst = φᴰ
      goal .snd = symP (subst (PathP _ fᴰ) φᴰ-sec fᴰ′-filler)

  isEssentiallySurjectiveDelooping : 𝔹Act.isLocallyEssentiallySurjective
  isEssentiallySurjectiveDelooping Xᴳ@(G , (X , σ)) Yᴴ@(H , (Y , τ)) = goal
    where module _ (f* @ (f , fᴰ) : SetBundle.hom (𝔹Act.₀ Xᴳ) (𝔹Act.₀ Yᴴ)) where
    open import Cubical.HITs.PropositionalTruncation.Monad
    open import Cubical.Categories.Category.Base using (CatIso ; pathToIso)
    goal : ∃[ φ* ∈ GroupAction.hom Xᴳ Yᴴ ] CatIso (LocalCategory _ (𝔹Act.₀ Xᴳ) (𝔹Act.₀ Yᴴ)) (𝔹Act.₁ φ*) f*
    goal = do
      (φ , φ-sec) ← LocalInverse.isSurjection-map f
      let (φᴰ , φᴰ-sec) = 𝔹ᴰ₁-sectionOver (X , σ) (Y , τ) f fᴰ φ φ-sec
      ∃-intro (φ , φᴰ) $ pathToIso $ Sigma.ΣPathP (φ-sec , φᴰ-sec)

  isLocallyWeakEquivalenceDelooping : 𝔹Act.isLocallyWeakEquivalence
  isLocallyWeakEquivalenceDelooping =
    𝔹Act.isLocallyFullyFaithful×EssentiallySurjective→isLocallyWeakEquivalence
      isLocallyFullyFaithfulDelooping
      isEssentiallySurjectiveDelooping
