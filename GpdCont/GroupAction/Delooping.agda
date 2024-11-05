{-# OPTIONS --lossy-unification #-}
module GpdCont.GroupAction.Delooping where

open import GpdCont.Prelude
open import GpdCont.Univalence using (ua ; ua→)

open import GpdCont.GroupAction.Base using (Action)
open import GpdCont.GroupAction.TwoCategory using (GroupActionᴰ ; GroupAction)
open import GpdCont.GroupAction.AssociatedBundle using (associatedBundle ; associatedBundleMap)
open import GpdCont.Group.TwoCategory using (TwoGroup)

open import GpdCont.SetBundle using (SetBundle ; SetBundleᴰ ; SetBundleᵀ)

import      GpdCont.Delooping.Base as Delooping
open import GpdCont.Delooping.Functor using (module TwoFunc)

open import GpdCont.TwoCategory.Base using (TwoCategory)
open import GpdCont.TwoCategory.LaxFunctor using (LaxFunctor)
open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryᴰ)
open import GpdCont.TwoCategory.Displayed.LaxFunctor using (LaxFunctorᴰ)
open import GpdCont.TwoCategory.Displayed.LocallyThin using (IntoLocallyThin)
open import GpdCont.TwoCategory.HomotopyGroupoid using (hGpdCat)

open import Cubical.Foundations.HLevels using (isOfHLevelPathP' ; isSet→)
open import Cubical.Foundations.Path using (compPath→Square)

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
--  ∙ 𝔹₀, assigning to a group action its associated bundle,
--  ∙ 𝔹₁, assigning to an equivariant map its associated map of bundles
--  ∙ 𝔹₂, assigning to a conjugator of actions a homotopy of bundle maps
--
-- ...and proofs that 𝔹 (laxly) preserves identity 2-cells and vertical composites.
module _ (ℓ : Level) where
  private
    module Group = TwoCategory (TwoGroup ℓ)
    module GroupActionᴰ = TwoCategoryᴰ (GroupActionᴰ ℓ)
    module hGpdCat = TwoCategory (hGpdCat ℓ)
    module SetBundleᴰ = TwoCategoryᴰ (SetBundleᴰ ℓ)

    open Delooping.𝔹 using (⋆)
    𝔹 = TwoFunc.TwoDelooping ℓ
    module 𝔹 = LaxFunctor 𝔹

    -- To each group action, assign its associated bundle:
    𝔹₀ : ∀ {G} → GroupActionᴰ.ob[ G ] → SetBundleᴰ.ob[ 𝔹.₀ G ]
    𝔹₀ (X , σ) = associatedBundle {X = X} σ

    -- Any equivariant map of group actions induces a map on associated bundles.
    𝔹₁ : ∀ {G H} {φ : Group.hom G H} {Xᴳ : GroupActionᴰ.ob[ G ]} {Yᴴ : GroupActionᴰ.ob[ H ]}
      → GroupActionᴰ.hom[ φ ] Xᴳ Yᴴ
      → SetBundleᴰ.hom[ 𝔹.₁ φ ] (𝔹₀ Xᴳ) (𝔹₀ Yᴴ)
    𝔹₁ (f , f-eqva) = associatedBundleMap _ _ _ f f-eqva

    -- Path lemma for producing displayed homotopies of set bundle maps
    -- with a delooping in their codomain.  Such homotopies are defined
    -- pointwise in the delooping; and since the target is a proposition
    -- (SetBundleᴰ is locally thin), it suffices to give the homotopy on
    -- the point.
    𝔹₁PathP : ∀ {G} {Y} {f g : hGpdCat.hom (𝔹.₀ G) Y} {r : hGpdCat.rel f g}
      → {Xᴳ : GroupActionᴰ.ob[ G ]}
      → (yᴰ : SetBundleᴰ.ob[ Y ])
      → {fᴰ : SetBundleᴰ.hom[ f ] (𝔹₀ Xᴳ) yᴰ}
      → {gᴰ : SetBundleᴰ.hom[ g ] (𝔹₀ Xᴳ) yᴰ}
      → (p⋆ : PathP (λ i → ⟨ yᴰ (r i ⋆) ⟩ → ⟨ 𝔹₀ Xᴳ ⋆ ⟩) (fᴰ ⋆) (gᴰ ⋆))
      → SetBundleᴰ.rel[_] {yᴰ = yᴰ} r fᴰ gᴰ
    𝔹₁PathP {G} {r} {Xᴳ} yᴰ {fᴰ} {gᴰ} p⋆ = funExt 𝔹₁PathP-ext where
      open Delooping ⟨ G ⟩ (str G) using (elimProp)

      isPropMotive : ∀ x → isProp (PathP (λ i → ⟨ yᴰ (r i x) ⟩ → ⟨ 𝔹₀ Xᴳ x ⟩) (fᴰ x) (gᴰ x))
      isPropMotive x = isOfHLevelPathP' 1 (isSet→ is-set-𝔹₀) _ _ where
        is-set-𝔹₀ : isSet ⟨ 𝔹₀ Xᴳ x ⟩
        is-set-𝔹₀ = str $ 𝔹₀ Xᴳ x

      𝔹₁PathP-ext : (x : ⟨ 𝔹.₀ G ⟩) → PathP (λ i → ⟨ yᴰ (r i x) ⟩ → ⟨ 𝔹₀ Xᴳ x ⟩) (fᴰ x) (gᴰ x)
      𝔹₁PathP-ext = elimProp isPropMotive p⋆


    -- A conjugator relating two equivariant maps induces a homotopy of associated bundle maps.
    -- It suffices to give the homotopy at the point, since 2-cells are propositional.  There,
    -- the goal becomes to show that maps are identified over a permutation of their domain.
    -- But a conjugator of equivariant maps supplies exactly this evidence.
    𝔹₂ : ∀ {G H} {φ ψ : Group.hom G H} {r : Group.rel φ ψ}
      → {Xᴳ : GroupActionᴰ.ob[ G ]} {Yᴴ : GroupActionᴰ.ob[ H ]}
      → {fᴰ : GroupActionᴰ.hom[ φ ] Xᴳ Yᴴ}
      → {gᴰ : GroupActionᴰ.hom[ ψ ] Xᴳ Yᴴ}
      → GroupActionᴰ.rel[ r ] fᴰ gᴰ
      → SetBundleᴰ.rel[_] {yᴰ = 𝔹₀ Yᴴ} (𝔹.₂ r) (𝔹₁ fᴰ) (𝔹₁ gᴰ)
    𝔹₂ {G} {r = r , _} {Xᴳ = X , _} {Yᴴ = Yᴴ @ (_ , τ) } {fᴰ = fᴰ @ (f , _)} {gᴰ = gᴰ @ (g , _)} rᴰ = 𝔹₁PathP (𝔹₀ Yᴴ) 𝔹₂-⋆ where
      module τ = Action τ
      -- `rᴰ` is evidence that `r` is a conjugator of `f` and `g`.
      -- This gives an identification of the associated bundle maps at the point.
      𝔹₂-⋆ : PathP (λ i → ua (τ.action r) i → ⟨ X ⟩) f g
      𝔹₂-⋆ = ua→ (funExt⁻ rᴰ)

      -- XXX: All three of 𝔹₁PathP, ua→, and funExt⁻ are equivalences of types.
      -- This means that 𝔹₂ is locally fully faithful.

    -- On the point, 𝔹 stricly preserves vertical composition of 2-cells...
    𝔹-trans-lax : ∀ {G H K} {φ : Group.hom G H} {ψ : Group.hom H K}
      → {Xᴳ : GroupActionᴰ.ob[ G ]}
      → {Yᴴ : GroupActionᴰ.ob[ H ]}
      → {Zᴷ : GroupActionᴰ.ob[ K ]}
      → (fᴰ : GroupActionᴰ.hom[ φ ] Xᴳ Yᴴ)
      → (gᴰ : GroupActionᴰ.hom[ ψ ] Yᴴ Zᴷ)
      → SetBundleᴰ.rel[_] {yᴰ = 𝔹₀ Zᴷ} (𝔹.F-trans-lax φ ψ) (SetBundleᴰ.comp-homᴰ {zᴰ = 𝔹₀ Zᴷ} (𝔹₁ fᴰ) (𝔹₁ gᴰ)) (𝔹₁ (fᴰ GroupActionᴰ.∙₁ᴰ gᴰ))
    𝔹-trans-lax {Zᴷ} (f , _) (g , _) = 𝔹₁PathP (𝔹₀ Zᴷ) $ refl′ (f ∘ g)

    -- ...and similarly for identity 2-cells:
    𝔹-id-lax : ∀ {G}
      → (Xᴳ : GroupActionᴰ.ob[ G ])
      → SetBundleᴰ.rel[_] (𝔹.F-id-lax G) (SetBundleᴰ.id-homᴰ (𝔹₀ Xᴳ)) (𝔹₁ (GroupActionᴰ.id-homᴰ Xᴳ))
    𝔹-id-lax Xᴳ @ (X , σ) = 𝔹₁PathP (𝔹₀ Xᴳ) $ refl′ (id ⟨ X ⟩)

  -- The above data assembles into a lax functor (𝔹 : GroupAction → SetBundle).
  𝔹ᵀ : IntoLocallyThin 𝔹 (GroupActionᴰ ℓ) (SetBundleᵀ ℓ)
  𝔹ᵀ .IntoLocallyThin.F-obᴰ = 𝔹₀
  𝔹ᵀ .IntoLocallyThin.F-homᴰ = 𝔹₁
  𝔹ᵀ .IntoLocallyThin.F-relᴰ = 𝔹₂
  𝔹ᵀ .IntoLocallyThin.F-trans-laxᴰ = 𝔹-trans-lax
  𝔹ᵀ .IntoLocallyThin.F-id-laxᴰ = 𝔹-id-lax

  𝔹ᴰ : LaxFunctorᴰ 𝔹 (GroupActionᴰ ℓ) (SetBundleᴰ ℓ)
  𝔹ᴰ = IntoLocallyThin.toLaxFunctorᴰ 𝔹ᵀ

  Delooping : LaxFunctor (GroupAction ℓ) (SetBundle ℓ)
  Delooping = LaxFunctorᴰ.toTotalFunctor 𝔹ᴰ
