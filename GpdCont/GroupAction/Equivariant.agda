module GpdCont.GroupAction.Equivariant where

open import GpdCont.Prelude
open import GpdCont.GroupAction.Base

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom ; idGroupHom)
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level
    G H K : Group ℓ
    X Y Z : hSet ℓ
    σ : Action G X
    τ : Action H Y

open Action

private
  Grp×Setᵒᵖ[_,_] : (G×X H×Y : Group ℓ × hSet ℓ) → Type ℓ
  Grp×Setᵒᵖ[ (G , X) , (H , Y) ] = GroupHom G H × (⟨ Y ⟩ → ⟨ X ⟩)
  {-# INJECTIVE_FOR_INFERENCE Grp×Setᵒᵖ[_,_] #-}

  compGrp×Setᵒᵖ : ∀ {G H K : Group ℓ} {X Y Z : hSet ℓ}
    → Grp×Setᵒᵖ[ (G , X) , (H , Y) ]
    → Grp×Setᵒᵖ[ (H , Y) , (K , Z) ]
    → Grp×Setᵒᵖ[ (G , X) , (K , Z) ]
  compGrp×Setᵒᵖ (φ , fᵒᵖ) (ψ , gᵒᵖ) .fst = compGroupHom φ ψ
  compGrp×Setᵒᵖ (φ , fᵒᵖ) (ψ , gᵒᵖ) .snd = fᵒᵖ ∘ gᵒᵖ

isEquivariantMap[_][_,_] :
  (φ×fᵒᵖ : Grp×Setᵒᵖ[ (G , X) , (H , Y) ])
  → Action G X → Action H Y → Type _
isEquivariantMap[ (φ , _) , fᵒᵖ ][ σ , τ ] = ∀ g → (σ ⁺ g) ∘ fᵒᵖ ≡ fᵒᵖ ∘ (τ ⁺ φ g)

{-# INJECTIVE_FOR_INFERENCE isEquivariantMap[_][_,_] #-}

opaque
  isPropIsEquivariantMap : (φ×fᵒᵖ : Grp×Setᵒᵖ[ (G , X) , (H , Y) ])
    → (σ : Action G X)
    → (τ : Action H Y)
    → isProp (isEquivariantMap[ φ×fᵒᵖ ][ σ , τ ])
  isPropIsEquivariantMap {X = X} _ _ _ = isPropΠ λ g → isSet→ (str X) _ _

opaque
  isEquivariantMap-comp :
    ∀ (φ×f : Grp×Setᵒᵖ[ (G , X) , (H , Y) ])
    → (ψ×p : Grp×Setᵒᵖ[ (H , Y) , (K , Z) ])
    → (σ : Action G X) (τ : Action H Y) (υ : Action K Z)
    → isEquivariantMap[ φ×f ][ σ , τ ]
    → isEquivariantMap[ ψ×p ][ τ , υ ]
    → isEquivariantMap[ compGrp×Setᵒᵖ {X = X} {Y = Y} {Z = Z} φ×f ψ×p ][ σ , υ ]
  isEquivariantMap-comp ((φ , _) , f) ((ψ , _) , p) σ τ υ f-eqva p-eqva g =
    (σ ⁺ g) ∘ f ∘ p ≡⟨ cong (_∘ p) (f-eqva g) ⟩
    f ∘ (τ ⁺ (φ g)) ∘ p ≡⟨ cong (f ∘_) (p-eqva (φ g)) ⟩
    f ∘ p ∘ (υ ⁺ (ψ (φ g))) ∎

isEquivariantMap-id : ∀ (σ : Action G X) → isEquivariantMap[ idGroupHom {G = G} , (id ⟨ X ⟩) ][ σ , σ ]
isEquivariantMap-id σ = λ g → refl
