module GpdCont.GroupAction.AssociatedBundle where

open import GpdCont.Prelude hiding (_▷_)
open import GpdCont.Univalence using (ua ; ua→ua ; ua→uaEquiv ; ua→ ; ua-gluePath)
open import GpdCont.GroupAction.Base using (Action ; _⁺_ ; module ActionProperties)
open import GpdCont.Delooping using (𝔹)
open import GpdCont.Delooping.Map using (map)
open import GpdCont.GroupAction.Equivariant using (isEquivariantMap[_][_,_])

open import Cubical.Foundations.Equiv as Equiv using (equivFun ; invEquiv ; invEquiv-is-rinv ; invEquiv-is-linv ; _∙ₑ_)
open import Cubical.Foundations.HLevels as HLevels using (hSet)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path as Path using ()
open import Cubical.Functions.FunExtEquiv using (funExtEquiv)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base using (Group ; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.SetQuotients as SQ using (_/_)

module _ {ℓ} {G : Group ℓ} {X : hSet ℓ} (σ : Action G X) where
  private
    module 𝔹G = GpdCont.Delooping G
    module σ = Action σ

  associatedBundle : 𝔹 G → hSet ℓ
  associatedBundle = 𝔹G.rec→hSet X σ.action σ.pres·

  {- (Judgemental) computation rules for associated bundles. -}

  -- Over the point, the fiber of the associated bundle is the given G-set.
  associatedBundle-⋆ : associatedBundle 𝔹G.⋆ ≡ X
  associatedBundle-⋆ = refl

  -- Over a loop, the action defines the path of type X ≡ X.
  associatedBundle-loop : ∀ g → cong (⟨_⟩ ∘ associatedBundle) (𝔹G.loop g) ≡ ua (σ.action g)
  associatedBundle-loop g = refl

module _ {ℓ} {G H : Group ℓ} {X Y : hSet ℓ} where
  private
    module 𝔹G = GpdCont.Delooping G

  module _ (σ : Action G X) (τ : Action H Y) (φ : GroupHom G H) where
    BundleMaps : 𝔹 G → Type _
    BundleMaps x = ⟨ associatedBundle τ (map φ x) ⟩ → ⟨ associatedBundle σ x ⟩

    isSetBundleMaps : ∀ x → isSet (BundleMaps x)
    isSetBundleMaps x = HLevels.isSet→ (str (associatedBundle σ x))

    isEquivariantMap≃BundleMapsPathP : (f : ⟨ Y ⟩ → ⟨ X ⟩)
      → isEquivariantMap[ φ , f ][ σ , τ ] ≃ (∀ g → PathP (λ i → BundleMaps (𝔹.loop g i)) f f)
    isEquivariantMap≃BundleMapsPathP f = Equiv.equivΠCod λ g →
      ((σ ⁺ g) ∘ f ≡ f ∘ (τ ⁺ (φ .fst g))) ≃⟨ invEquiv funExtEquiv ⟩
      (∀ y → ((σ ⁺ g) ∘ f $ y) ≡ (f ∘ (τ ⁺ (φ .fst g)) $ y)) ≃⟨ ua→uaEquiv {α = Action.action τ (φ .fst g)} {β = Action.action σ g} ⟩
      (PathP (λ i → BundleMaps (𝔹.loop g i)) f f) ≃∎

    associatedBundleMapEquiv :
      (Σ[ f ∈ (⟨ Y ⟩ → ⟨ X ⟩) ] isEquivariantMap[ φ , f ][ σ , τ ])
        ≃
      ((x : 𝔹 G) → ⟨ associatedBundle τ (map φ x) ⟩ → ⟨ associatedBundle σ x ⟩)
    associatedBundleMapEquiv = Σ-cong-equiv-snd isEquivariantMap≃BundleMapsPathP ∙ₑ 𝔹G.elimSetEquiv isSetBundleMaps

    associatedBundleMap : (f : ⟨ Y ⟩ → ⟨ X ⟩) → isEquivariantMap[ φ , f ][ σ , τ ] → (x : 𝔹 G) → ⟨ associatedBundle τ (map φ x) ⟩ → ⟨ associatedBundle σ x ⟩
    associatedBundleMap f is-eqva = equivFun associatedBundleMapEquiv (f , is-eqva)

    {- (Judgemental) computation rules for associated bundle map -}

    -- At the point, the associated bundle map evaluates to the given equivariant map.
    associatedBundleMap-⋆ : ∀ (f : (⟨ Y ⟩ → ⟨ X ⟩)) f-eqva → associatedBundleMap f f-eqva 𝔹.⋆ ≡ f
    associatedBundleMap-⋆ _ _ = refl

    -- Over a loop, the associated bundle map computes to the self-identification
    -- of an equivariant map with itself over the witness* of it being equivariant.
    associatedBundleMap-loop : ∀ (f : (⟨ Y ⟩ → ⟨ X ⟩)) (f-eqva : isEquivariantMap[ φ , f ][ σ , τ ])
      → ∀ (g : ⟨ G ⟩)
      → Path (PathP _ f f)
          (cong (associatedBundleMap f f-eqva) (𝔹G.loop g))
          (ua→ua (funExt⁻ (f-eqva g)))
    associatedBundleMap-loop _ _ g = refl

module _ {ℓ} {G : Group ℓ} {X : hSet ℓ} (σ : Action G X) where
  private
    module G = GroupStr (str G)
    𝔹G = GpdCont.Delooping.𝔹 G
    module 𝔹G = GpdCont.Delooping G
    open module σ = Action σ using (_▷_)

    -- Total space of the associated bundle (Symmetry 4.7.13)
    ∫σ : Type _
    ∫σ = Σ[ x ∈ 𝔹G ] ⟨ associatedBundle σ x ⟩

  _∼_ : (x y : ⟨ X ⟩) → Type ℓ
  x ∼ y = ∃[ g ∈ ⟨ G ⟩ ] g ▷ x ≡ y

  Orbits : Type _
  Orbits = ⟨ X ⟩ / _∼_

  isSetOrbits : isSet Orbits
  isSetOrbits = SQ.squash/

  private
    ∼-intro-right : (g : ⟨ G ⟩) (x : ⟨ X ⟩) → x ∼ (g ▷ x)
    ∼-intro-right g x = ∃-intro g goal where
      goal : g ▷ x ≡ g ▷ x
      goal = refl

  associatedBundleComponents→Orbits : (x : 𝔹G) → ⟨ associatedBundle σ x ⟩ → Orbits
  associatedBundleComponents→Orbits = 𝔹G.elimSet (λ x → HLevels.isSet→ isSetOrbits) f⋆ f-loop where
    f⋆ : ⟨ X ⟩ → Orbits
    f⋆ = SQ.[_]

    f-rel : ∀ g x → x ∼ (σ ⁺ g) x
    f-rel = ∼-intro-right

    f-loop : ∀ g → PathP (λ i → ua (σ.action g) i → Orbits) f⋆ f⋆
    f-loop g = ua→ λ x → SQ.eq/ _ _ (f-rel g x)

  Orbits→associatedBundleComponents : Orbits → ∥ Σ[ x ∈ 𝔹G ] ⟨ associatedBundle σ x ⟩ ∥₂
  Orbits→associatedBundleComponents = SQ.rec ST.isSetSetTrunc rep rep-well-defined where
    rep : ⟨ X ⟩ → ∥ Σ[ x ∈ 𝔹G ] ⟨ associatedBundle σ x ⟩ ∥₂
    rep x = ST.∣ 𝔹G.⋆ , x ∣₂

    rep-well-defined : (x y : ⟨ X ⟩) → x ∼ y → rep x ≡ rep y
    rep-well-defined x y = ∃-rec (ST.isSetSetTrunc (rep x) (rep y)) goal where
      glue-σ : {g : ⟨ G ⟩} → g ▷ x ≡ y → PathP (λ i → ua (σ.action g) i) x y
      glue-σ {g} p = ua-gluePath (σ.action g) p

      goal : (g : ⟨ G ⟩) → g ▷ x ≡ y → ST.∣ 𝔹G.⋆ , x ∣₂ ≡ ST.∣ (𝔹G.⋆ , y) ∣₂
      goal g p = cong ST.∣_∣₂ $ ΣPathP (𝔹G.loop g , glue-σ p)

  associatedBundleComponents-Orbits-Iso : Iso ∥ Σ[ x ∈ 𝔹G ] ⟨ associatedBundle σ x ⟩ ∥₂ Orbits
  associatedBundleComponents-Orbits-Iso .Iso.fun = ST.rec isSetOrbits $ uncurry associatedBundleComponents→Orbits
  associatedBundleComponents-Orbits-Iso .Iso.inv = Orbits→associatedBundleComponents
  associatedBundleComponents-Orbits-Iso .Iso.sec = SQ.elimProp (λ orbit → isSetOrbits _ orbit) λ _ → refl
  associatedBundleComponents-Orbits-Iso .Iso.ret = ST.elim (λ comp → ST.isSetPathImplicit) $ uncurry goal where
    goal : (x : 𝔹G) → (y : ⟨ associatedBundle σ x ⟩) → Orbits→associatedBundleComponents (associatedBundleComponents→Orbits x y) ≡ ST.∣ x , y ∣₂
    goal = 𝔹G.elimProp (λ x → HLevels.isPropΠ λ y → ST.isSetSetTrunc _ _) λ _ → refl

  associatedBundleComponents≃Orbits : ∥ Σ[ x ∈ 𝔹G ] ⟨ associatedBundle σ x ⟩ ∥₂ ≃ Orbits
  associatedBundleComponents≃Orbits = isoToEquiv associatedBundleComponents-Orbits-Iso
