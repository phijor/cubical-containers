module GpdCont.GroupAction.AssociatedBundle where

open import GpdCont.Prelude
open import GpdCont.Univalence using (ua ; ua→ua)
open import GpdCont.GroupAction.Base using (Action ; _⁺_)
open import GpdCont.Delooping.Base using (𝔹)
open import GpdCont.Delooping.Map using (map)
open import GpdCont.GroupAction.Equivariant using (isEquivariantMap[_][_,_])

open import Cubical.Foundations.Equiv using (equivFun)
open import Cubical.Foundations.HLevels as HLevels using (hSet)
open import Cubical.Algebra.Group.Base using (Group)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)

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
