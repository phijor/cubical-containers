module GpdCont.GroupAction.AssociatedBundle where

open import GpdCont.Prelude hiding (_▷_)
open import GpdCont.Univalence using (ua ; ua→ua ; ua→ ; ua-gluePath)
open import GpdCont.GroupAction.Base using (Action ; _⁺_ ; module ActionProperties)
open import GpdCont.Delooping.Base using (𝔹)
open import GpdCont.Delooping.Map using (map)
open import GpdCont.GroupAction.Equivariant using (isEquivariantMap[_][_,_])

open import Cubical.Foundations.Equiv as Equiv using (equivFun ; invEquiv-is-rinv ; invEquiv-is-linv)
open import Cubical.Foundations.HLevels as HLevels using (hSet)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path as Path using ()
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base using (Group ; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.SetQuotients as SQ using (_/_)

module _ {ℓ} {G : Group ℓ} {X : hSet ℓ} (σ : Action G X) where
  private
    module 𝔹G = GpdCont.Delooping.Base ⟨ G ⟩ (str G)
    module σ = Action σ

  associatedBundle : 𝔹 ⟨ G ⟩ (str G) → hSet ℓ
  associatedBundle = 𝔹G.rec→hSet X σ.action σ.pres·

module _ {ℓ} {G H : Group ℓ} {X Y : hSet ℓ} where
  associatedBundleMap : (σ : Action G X) (τ : Action H Y)
    → (φ : GroupHom G H) (f : ⟨ Y ⟩ → ⟨ X ⟩)
    → isEquivariantMap[ φ , f ][ σ , τ ]
    → (x : 𝔹 ⟨ G ⟩ (str G)) → ⟨ associatedBundle τ (map φ x) ⟩ → ⟨ associatedBundle σ x ⟩
  associatedBundleMap σ τ φ f is-eqva = 𝔹G.elimSet {B = Motive} isSetMotive map⋆ map-comp where
    module 𝔹G = GpdCont.Delooping.Base ⟨ G ⟩ (str G)
    module σ = Action σ
    module τ = Action τ

    Motive : 𝔹G.𝔹 → Type _
    Motive x = ⟨ associatedBundle τ (map φ x) ⟩ → ⟨ associatedBundle σ x ⟩

    isSetMotive : ∀ x → isSet (Motive x)
    isSetMotive x = HLevels.isSet→ (str (associatedBundle σ x))

    map⋆ : ⟨ Y ⟩ → ⟨ X ⟩
    map⋆ = f

    map-comp′ : ∀ g (y : ⟨ Y ⟩) → (σ ⁺ g) (f y) ≡ f ((τ ⁺ φ .fst g) y)
    map-comp′ g y = is-eqva g ≡$ y

    map-comp : ∀ g → PathP (λ i → ua (τ.action (φ .fst g)) i → ua (σ.action g) i) map⋆ map⋆
    map-comp g = ua→ua $ map-comp′ g

module _ {ℓ} {G : Group ℓ} {X : hSet ℓ} (σ : Action G X) where
  private
    module G = GroupStr (str G)
    𝔹G = GpdCont.Delooping.Base.𝔹 ⟨ G ⟩ (str G)
    module 𝔹G = GpdCont.Delooping.Base ⟨ G ⟩ (str G)
    open module σ = Action σ using (_▷_)

    -- Total space of the associated bundle (Symmetry 4.7.13)
    ∫σ : Type _
    ∫σ = Σ[ x ∈ 𝔹G ] ⟨ associatedBundle σ x ⟩

    _∼_ : (x y : ⟨ X ⟩) → Type ℓ
    x ∼ y = ∃[ g ∈ ⟨ G ⟩ ] g ▷ x ≡ y

    ∼-intro-right : (g : ⟨ G ⟩) (x : ⟨ X ⟩) → x ∼ (g ▷ x)
    ∼-intro-right g x = ∃-intro g goal where
      goal : g ▷ x ≡ g ▷ x
      goal = refl -- (sym $ ActionProperties.action-cancel-right σ g) ≡$ x

    Orbits : Type _
    Orbits = ⟨ X ⟩ / _∼_

    isSetOrbits : isSet Orbits
    isSetOrbits = SQ.squash/

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
  associatedBundleComponents-Orbits-Iso .Iso.rightInv = SQ.elimProp (λ orbit → isSetOrbits _ orbit) λ _ → refl
  associatedBundleComponents-Orbits-Iso .Iso.leftInv = ST.elim (λ comp → ST.isSetPathImplicit) $ uncurry goal where
    goal : (x : 𝔹G) → (y : ⟨ associatedBundle σ x ⟩) → Orbits→associatedBundleComponents (associatedBundleComponents→Orbits x y) ≡ ST.∣ x , y ∣₂
    goal = 𝔹G.elimProp (λ x → HLevels.isPropΠ λ y → ST.isSetSetTrunc _ _) λ _ → refl

  associatedBundleComponents≃Orbits : ∥ Σ[ x ∈ 𝔹G ] ⟨ associatedBundle σ x ⟩ ∥₂ ≃ Orbits
  associatedBundleComponents≃Orbits = isoToEquiv associatedBundleComponents-Orbits-Iso
