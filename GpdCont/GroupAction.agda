module GpdCont.GroupAction where

open import GpdCont.Prelude
open import GpdCont.Groups.Base
open import GpdCont.Groups.Homomorphism
open import GpdCont.SetQuotients using (SetTrunc≃SetQuotientPath ; relBiimpl→QuotIso)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.SetQuotients as SQ using (_/_)

record Action {ℓ} (BG : Group ℓ) : Type (ℓ-suc ℓ) where
  private
    module BG = GroupStr (str BG)

  field
    action : ⟨ BG ⟩ → hSet ℓ

  _⦅_⦆ : (g : ⟨ BG ⟩) → Type ℓ
  _⦅_⦆ g = ⟨ action g ⟩

  _⋆ : Type ℓ
  _⋆ = _⦅_⦆ BG.pt

  _⋆Set : hSet ℓ
  _⋆Set = action BG.pt

  is-set-⦅_⦆ : ∀ g → isSet (_⦅_⦆ g)
  is-set-⦅_⦆ = str ∘ action

module _ {ℓ} (BG : Group ℓ) (X : Action BG) where
  open Action

  module BG = GroupStr (str BG)

  OrbitGroupoid : Type ℓ
  OrbitGroupoid = Σ[ g ∈ ⟨ BG ⟩ ] X ⦅ g ⦆

  Orbit : Type ℓ
  Orbit = ∥ OrbitGroupoid ∥₂

  isSetOrbit : isSet Orbit
  isSetOrbit = ST.isSetSetTrunc

  -- isEquivariantᴰ : ∀ {g h} (x : X ⦅ g ⦆) → (y : X ⦅ h ⦆) → Type _
  -- isEquivariantᴰ {g} {h} x y = Σ[ p ∈ (g ≡ h) ] PathP (λ i → X ⦅ p i ⦆) x y

  -- isEquivariant : ∀ (x y : X ⋆) → Type _
  -- isEquivariant = isEquivariantᴰ

  {-
  OrbitEquivariantQuotientIso : Iso Orbit ((X ⋆) / isEquivariant)
  OrbitEquivariantQuotientIso .Iso.fun = ST.rec SQ.squash/ (uncurry trp) where
    goal : (x : X ⋆) → (X ⋆) / isEquivariant
    goal = SQ.[_]

    trp∞ : (g : ⟨ BG ⟩) (p : g ≡ BG.pt) (x : X ⦅ g ⦆) → (X ⋆) / isEquivariant
    trp∞ g p x = goal $ subst (X ⦅_⦆) p x

    trp∞-const : ∀ g → (p q : g ≡ BG.pt) → trp∞ g p ≡ trp∞ g q
    trp∞-const g p q = funExt λ x → SQ.eq/ _ _ (lem x) where
      lem : ∀ x → isEquivariant (subst (_⦅_⦆ X) p x) (subst (_⦅_⦆ X) q x)
      lem x .fst = sym p ∙ q
      lem x .snd = compPathP' {B = X ⦅_⦆} {y' = x} {p = sym p} {q = q}
        (symP-fromGoal $ subst-filler (X ⦅_⦆) p x)
        (subst-filler (X ⦅_⦆) q x)

    trp : (g : ⟨ BG ⟩) (x : X ⦅ g ⦆) → (X ⋆) / isEquivariant
    trp g = PT.rec→Set (isSet→ SQ.squash/) (trp∞ g) (trp∞-const g) (BG.existsPath g BG.pt)

  OrbitEquivariantQuotientIso .Iso.inv = SQ.rec isSetOrbit orb orb-eq where
    orb : X ⋆ → Orbit
    orb x = ST.∣ BG.pt , x ∣₂

    orb-eq : (x y : X ⋆) → isEquivariant x y → orb x ≡ orb y
    orb-eq x y (p , q) = cong ST.∣_∣₂ (ΣPathP (p , q))
  OrbitEquivariantQuotientIso .Iso.rightInv = SQ.elimProp (λ _ → SQ.squash/ _ _)
    λ (x : X ⋆) → {! here be transport hell !}
  OrbitEquivariantQuotientIso .Iso.leftInv = ST.elim {! !} {! !}
  -}

  _≈_ : (x y : X ⋆) → Type _
  x ≈ y = Path OrbitGroupoid (BG.pt , x) (BG.pt , y)

  OrbitEquivariantQuotientEquiv : Orbit ≃ ((X ⋆) / _≈_)
  OrbitEquivariantQuotientEquiv =
    Orbit ≃⟨ SetTrunc≃SetQuotientPath ⟩
    OrbitGroupoid / _≡_ ≃⟨ {! !} ⟩
    ((X ⋆) / _≈_) ≃∎

module _ {ℓ} {G : Group ℓ} (X Y : Action G) where
  open Action

  Equivariant : Type _
  Equivariant = ∀ g → X ⦅ g ⦆ → Y ⦅ g ⦆

module _ where
  open Action

  pullbackAction : ∀ {ℓ} {G H : Group ℓ} (φ : GroupHom G H) (X : Action H) → Action G
  pullbackAction φ X .action = ⟪ φ ⟫ ⋆ X .action
