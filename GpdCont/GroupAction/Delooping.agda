{-# OPTIONS --lossy-unification #-}
module GpdCont.GroupAction.Delooping where

open import GpdCont.Prelude
open import GpdCont.Univalence using (ua ; ua→)

open import GpdCont.GroupAction.Base using (Action ; _⁺_ ; module ActionProperties)
open import GpdCont.GroupAction.Equivariant renaming (isEquivariantMap[_][_,_] to isEquivariantMap)
open import GpdCont.GroupAction.TwoCategory using (GroupActionᴰ ; GroupAction)
open import GpdCont.GroupAction.AssociatedBundle using (associatedBundle ; associatedBundleMap)
open import GpdCont.Group.TwoCategory using (TwoGroup)

open import GpdCont.SetBundle using (SetBundle ; SetBundleᴰ ; SetBundleᵀ)

import      GpdCont.Delooping as Delooping
open import GpdCont.Delooping.Functor using (module TwoFunc ; module LocalInverse)

open import GpdCont.TwoCategory.Base using (TwoCategory)
open import GpdCont.TwoCategory.LaxFunctor using (LaxFunctor)
open import GpdCont.TwoCategory.LocalCategory using (LocalCategory)
open import GpdCont.TwoCategory.LocalFunctor using (isLocallyFullyFaithful ; isLocallyEssentiallySurjective)
open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryᴰ)
open import GpdCont.TwoCategory.Displayed.LaxFunctor using (LaxFunctorᴰ)
open import GpdCont.TwoCategory.Displayed.LocallyThin using (IntoLocallyThin)
open import GpdCont.TwoCategory.HomotopyGroupoid using (hGpdCat)

open import Cubical.Foundations.Equiv using (isEquiv ; equivFun ; equivIsEquiv ; _∙ₑ_)
open import Cubical.Foundations.HLevels using (isOfHLevelPathP' ; isSet→)
open import Cubical.Foundations.Path using (compPath→Square)
open import Cubical.Functions.FunExtEquiv using (funExtEquiv)
import      Cubical.Data.Sigma as Sigma

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
    module GroupAction = TwoCategory (GroupAction ℓ)
    module GroupActionᴰ = TwoCategoryᴰ (GroupActionᴰ ℓ)
    module hGpdCat = TwoCategory (hGpdCat ℓ)
    module SetBundle = TwoCategory (SetBundle ℓ)
    module SetBundleᴰ = TwoCategoryᴰ (SetBundleᴰ ℓ)

    open Delooping.𝔹 using (⋆ ; loop)
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

    -- Path lemma characterizing displayed homotopies of set bundle maps
    -- with a delooping in their codomain.  Such homotopies are defined
    -- pointwise in the delooping; and since the target is a proposition
    -- (SetBundleᴰ is locally thin), it suffices to give the homotopy on
    -- the point.
    module _
      {G} {Y} {f g : hGpdCat.hom (𝔹.₀ G) Y} {r : hGpdCat.rel f g}
      {Xᴳ : GroupActionᴰ.ob[ G ]}
      (yᴰ : SetBundleᴰ.ob[ Y ])
      {fᴰ : SetBundleᴰ.hom[ f ] (𝔹₀ Xᴳ) yᴰ}
      {gᴰ : SetBundleᴰ.hom[ g ] (𝔹₀ Xᴳ) yᴰ}
      where
      open Delooping ⟨ G ⟩ (str G) using (elimPropEquiv)
      isProp𝔹₁PathP : ∀ x → isProp (PathP (λ i → ⟨ yᴰ (r i x) ⟩ → ⟨ 𝔹₀ Xᴳ x ⟩) (fᴰ x) (gᴰ x))
      isProp𝔹₁PathP x = isOfHLevelPathP' 1 (isSet→ is-set-𝔹₀) _ _ where
        is-set-𝔹₀ : isSet ⟨ 𝔹₀ Xᴳ x ⟩
        is-set-𝔹₀ = str $ 𝔹₀ Xᴳ x

      𝔹₁-PathPEquiv :
        (PathP (λ i → ⟨ yᴰ (r i ⋆) ⟩ → ⟨ 𝔹₀ Xᴳ ⋆ ⟩) (fᴰ ⋆) (gᴰ ⋆))
          ≃
        (∀ x → PathP (λ i → ⟨ yᴰ (r i x) ⟩ → ⟨ 𝔹₀ Xᴳ x ⟩) (fᴰ x) (gᴰ x))
      𝔹₁-PathPEquiv = elimPropEquiv isProp𝔹₁PathP

      𝔹₁-PathP≃SetBundleRel : (PathP (λ i → ⟨ yᴰ (r i ⋆) ⟩ → ⟨ 𝔹₀ Xᴳ ⋆ ⟩) (fᴰ ⋆) (gᴰ ⋆)) ≃ (SetBundleᴰ.rel[_] {yᴰ = yᴰ} r fᴰ gᴰ)
      𝔹₁-PathP≃SetBundleRel = 𝔹₁-PathPEquiv ∙ₑ funExtEquiv

      𝔹₁PathP : (p⋆ : PathP (λ i → ⟨ yᴰ (r i ⋆) ⟩ → ⟨ 𝔹₀ Xᴳ ⋆ ⟩) (fᴰ ⋆) (gᴰ ⋆))
        → SetBundleᴰ.rel[_] {yᴰ = yᴰ} r fᴰ gᴰ
      𝔹₁PathP = equivFun 𝔹₁-PathP≃SetBundleRel

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
      𝔹₂-equiv : (GroupActionᴰ.rel[ r ] fᴰ gᴰ) ≃ (SetBundleᴰ.rel[_] {yᴰ = 𝔹₀ Yᴴ} (𝔹.₂ r) (𝔹₁ fᴰ) (𝔹₁ gᴰ))
      𝔹₂-equiv =
        (GroupActionᴰ.rel[ r ] fᴰ gᴰ) ≃⟨ ActionProperties.uaExtEquiv τ (r .fst) ⟩
        (PathP (λ i → ⟨ 𝔹₀ Yᴴ (𝔹.₂ r i ⋆) ⟩ → ⟨ 𝔹₀ Xᴳ ⋆ ⟩) f g) ≃⟨ 𝔹₁-PathP≃SetBundleRel (𝔹₀ Yᴴ) ⟩
        (SetBundleᴰ.rel[_] {yᴰ = 𝔹₀ Yᴴ} (𝔹.₂ r) (𝔹₁ fᴰ) (𝔹₁ gᴰ)) ≃∎

      𝔹₂ : GroupActionᴰ.rel[ r ] fᴰ gᴰ → SetBundleᴰ.rel[_] {yᴰ = 𝔹₀ Yᴴ} (𝔹.₂ r) (𝔹₁ fᴰ) (𝔹₁ gᴰ)
      𝔹₂ = equivFun 𝔹₂-equiv

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

  private
    module 𝔹Act = LaxFunctor Delooping

  isLocallyFullyFaithfulDelooping : isLocallyFullyFaithful Delooping
  isLocallyFullyFaithfulDelooping σ τ f@(φ , _) g@(ψ , _) = goal where
    ∫𝔹₁ = LaxFunctor.F-hom Delooping

    ∫𝔹₂ : GroupAction.rel f g → SetBundle.rel (∫𝔹₁ f) (∫𝔹₁ g)
    ∫𝔹₂ = LaxFunctor.F-rel Delooping {f = f} {g = g}

    ∫𝔹₂-equiv : GroupAction.rel f g ≃ SetBundle.rel (∫𝔹₁ f) (∫𝔹₁ g)
    ∫𝔹₂-equiv = Sigma.Σ-cong-equiv
      (TwoFunc.localDeloopingEmbedding ℓ φ ψ)
       λ (r : Group.rel φ ψ) → 𝔹₂-equiv {r = r}

    goal : isEquiv ∫𝔹₂
    goal = equivIsEquiv ∫𝔹₂-equiv

  private
    open LocalInverse using (unmap ; unmap-section)
    module _
      {G H : Group.ob}
      {Xᴳ @ (X , σ) : GroupActionᴰ.ob[ G ]}
      {Yᴴ @ (Y , τ) : GroupActionᴰ.ob[ H ]}
      {Γ : hGpdCat.hom (𝔹.₀ G) (𝔹.₀ H)}
      (Γᴰ : SetBundleᴰ.hom[ Γ ] (𝔹₀ Xᴳ) (𝔹₀ Yᴴ))
      (Γ⋆-comp : Γ ⋆ ≡ ⋆)
      where
      φ = unmap Γ Γ⋆-comp
      φ-sec = unmap-section Γ Γ⋆-comp

      Γᴰ⋆ : ⟨ 𝔹₀ Yᴴ (Γ ⋆) ⟩ → ⟨ X ⟩
      Γᴰ⋆ = Γᴰ ⋆

      fixit : ⟨ 𝔹₀ Yᴴ ⋆ ⟩ ≡ ⟨ 𝔹₀ Yᴴ (Γ ⋆) ⟩
      fixit = cong (λ x → ⟨ 𝔹₀ Yᴴ x ⟩) (sym Γ⋆-comp)

      φᴰ : Σ[ f ∈ (⟨ Y ⟩ → ⟨ X ⟩) ] isEquivariantMap (φ , f) σ τ
      φᴰ .fst = Γᴰ⋆ ∘ transport fixit
      φᴰ .snd g = goal where
        pᴰ : PathP (λ i → ⟨ 𝔹₀ Yᴴ (Γ (loop g i)) ⟩ → ⟨ 𝔹₀ Xᴳ (loop g i) ⟩) Γᴰ⋆ Γᴰ⋆
        pᴰ = cong Γᴰ (loop g)

        goal : (σ ⁺ g) ∘ (Γᴰ⋆ ∘ transport fixit) ≡ Γᴰ⋆ ∘ transport fixit ∘ (τ ⁺ (φ .fst g))
        goal = {! fromPathP pᴰ !}

      𝔹₁-sectionOver : Σ[ φᴰ ∈ GroupActionᴰ.hom[ φ ] Xᴳ Yᴴ ] PathP (λ i → SetBundleᴰ.hom[ φ-sec i ] (𝔹₀ Xᴳ) (𝔹₀ Yᴴ)) (𝔹₁ φᴰ) Γᴰ
      𝔹₁-sectionOver .fst = φᴰ
      𝔹₁-sectionOver .snd = {! !}

  isEssentiallySurjectiveDelooping : isLocallyEssentiallySurjective Delooping
  isEssentiallySurjectiveDelooping Xᴳ@(G , (X , σ)) Yᴴ@(H , (Y , τ)) = goal
    where module _ (Γ* @ (Γ , Γᴰ) : SetBundle.hom (𝔹Act.₀ Xᴳ) (𝔹Act.₀ Yᴴ)) where
    open import Cubical.HITs.PropositionalTruncation.Monad
    open import Cubical.Categories.Category.Base using (CatIso ; pathToIso)
    goal : ∃[ φ* ∈ GroupAction.hom Xᴳ Yᴴ ] CatIso (LocalCategory _ (𝔹Act.₀ Xᴳ) (𝔹Act.₀ Yᴴ)) (𝔹Act.₁ φ*) Γ*
    goal = do
      Γ⋆-comp ← Delooping.merePath ⟨ H ⟩ (str H) (Γ ⋆) ⋆
      -- Γ⋆-comp : Γ ⋆ ≡ ⋆
      let
        (φ , p) = LocalInverse.conjugateSection-map Γ Γ⋆-comp
        (φᴰ , pᴰ) = 𝔹₁-sectionOver Γᴰ Γ⋆-comp
      ∃-intro (φ , φᴰ) $ pathToIso $ Sigma.ΣPathP (p , pᴰ)
