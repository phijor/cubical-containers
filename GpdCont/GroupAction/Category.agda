{-# OPTIONS --lossy-unification #-}
module GpdCont.GroupAction.Category where

open import GpdCont.Prelude
open import GpdCont.GroupAction.Base

open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma as Sigma using ()

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Categories.Category.Base using (Category ; _^op ; _[_,_] ; seq')
open import Cubical.Categories.Instances.Groups using (GroupCategory)
open import Cubical.Categories.Displayed.Base as Catᴰ using (Categoryᴰ)

module _ {ℓ : Level} where
  private
    Grpᵒᵖ : Category (ℓ-suc ℓ) ℓ
    Grpᵒᵖ = GroupCategory ^op

    variable
      G H K : Group ℓ
      X Y Z : hSet ℓ

  open Categoryᴰ
  open Action

  isEquivariantMap : (φ : Grpᵒᵖ [ H , G ]) (τ : Action H Y) (σ : Action G X) (f : ⟨ Y ⟩ → ⟨ X ⟩) → Type _
  isEquivariantMap (φ , _) τ σ f = ∀ g → (σ ⁺ g) ∘ f ≡ f ∘ (τ ⁺ φ g)

  isPropIsEquivariantMap : (φ : Grpᵒᵖ [ H , G ]) → {τ : Action H Y} {σ : Action G X} (f : ⟨ Y ⟩ → ⟨ X ⟩) → isProp (isEquivariantMap φ τ σ f)
  isPropIsEquivariantMap {X = X} φ f = isPropΠ λ g → isSet→ (str X) _ _

  isEquivariantMap-comp : (ψ : Grpᵒᵖ [ K , H ]) (φ : Grpᵒᵖ [ H , G ])
    → (σ : Action G X) (τ : Action H Y) (υ : Action K Z)
    (e : ⟨ Z ⟩ → ⟨ Y ⟩)
    (f : ⟨ Y ⟩ → ⟨ X ⟩)
    → isEquivariantMap ψ υ τ e
    → isEquivariantMap φ τ σ f
    → isEquivariantMap (ψ ⋆⟨ Grpᵒᵖ ⟩ φ) υ σ (f ∘ e)
  isEquivariantMap-comp (ψ , _) (φ , _) σ τ υ e f e-eqva f-eqva = λ g →
    (σ ⁺ g) ∘ f ∘ e ≡⟨ cong (_∘ e) (f-eqva g) ⟩
    f ∘ (τ ⁺ (φ g)) ∘ e ≡⟨ cong (f ∘_) (e-eqva (φ g)) ⟩
    f ∘ e ∘ (υ ⁺ (ψ (φ g))) ∎

  w = {!Catᴰ.weakenᴰ !}
  -- Actionᴰ' : Categoryᴰ Grpᵒᵖ _ ℓ
  -- Actionᴰ' .ob[_] G = Σ[ X ∈ hSet ℓ ] Action G X
  -- Actionᴰ' .Hom[_][_,_] {x = H} {y = G} φᵒᵖ (Y , τ) (X , σ) = Σ[ f ∈ (⟨ Y ⟩ → ⟨ X ⟩) ] isEquivariantMap φᵒᵖ τ σ f
  -- Actionᴰ' .idᴰ {x = G} {p = (X , σ)} = id ⟨ X ⟩ , λ (g : ⟨ G ⟩) → refl
  -- Actionᴰ' ._⋆ᴰ_ {x = K} {y = H} {z = G} {f = ψ} {g = φ} {xᴰ = (Z , υ)} {yᴰ = (Y , τ)} {zᴰ = (X , σ)} (e , e-eqva) (f , f-eqva) = f ∘ e , isEquivariantMap-comp ψ φ σ τ υ e f e-eqva f-eqva
  -- Actionᴰ' .⋆IdLᴰ {f = φ} (f , f-eqva) = Sigma.ΣPathPProp (isPropIsEquivariantMap φ) $ refl′ f
  -- Actionᴰ' .⋆IdRᴰ {f = φ} (f , f-eqva) = Sigma.ΣPathPProp (isPropIsEquivariantMap φ) $ refl′ f
  -- Actionᴰ' .⋆Assocᴰ {f = ω} {g = ψ} {h = φ} (f , _) (g , _) (h , _) = Sigma.ΣPathPProp (isPropIsEquivariantMap (ω ⋆⟨ Grpᵒᵖ ⟩ ψ ⋆⟨ Grpᵒᵖ ⟩ φ)) $ refl′ (h ∘ g ∘ f)
  -- Actionᴰ' .isSetHomᴰ {f = φ} {yᴰ = (Y , τ)} = isSetΣSndProp (isSet→ (str Y)) (isPropIsEquivariantMap φ)

  Actionᴰ : Categoryᴰ Grpᵒᵖ _ ℓ
  Actionᴰ .ob[_] G = Σ[ X ∈ hSet ℓ ] Action G X
  Actionᴰ .Hom[_][_,_] {x = H} {y = G} φᵒᵖ (Y , τ) (X , σ) = Σ[ f ∈ (⟨ Y ⟩ → ⟨ X ⟩) ] isEquivariantMap φᵒᵖ τ σ f
  Actionᴰ .idᴰ {x = G} {p = (X , σ)} = id ⟨ X ⟩ , λ (g : ⟨ G ⟩) → refl
  Actionᴰ ._⋆ᴰ_ {x = K} {y = H} {z = G} {f = ψ} {g = φ} {xᴰ = (Z , υ)} {yᴰ = (Y , τ)} {zᴰ = (X , σ)} (e , e-eqva) (f , f-eqva) = f ∘ e , isEquivariantMap-comp ψ φ σ τ υ e f e-eqva f-eqva
  Actionᴰ .⋆IdLᴰ {f = φ} (f , f-eqva) = Sigma.ΣPathPProp (isPropIsEquivariantMap φ) $ refl′ f
  Actionᴰ .⋆IdRᴰ {f = φ} (f , f-eqva) = Sigma.ΣPathPProp (isPropIsEquivariantMap φ) $ refl′ f
  Actionᴰ .⋆Assocᴰ {f = ω} {g = ψ} {h = φ} (f , _) (g , _) (h , _) = Sigma.ΣPathPProp (isPropIsEquivariantMap (ω ⋆⟨ Grpᵒᵖ ⟩ ψ ⋆⟨ Grpᵒᵖ ⟩ φ)) $ refl′ (h ∘ g ∘ f)
  Actionᴰ .isSetHomᴰ {f = φ} {yᴰ = (Y , τ)} = isSetΣSndProp (isSet→ (str Y)) (isPropIsEquivariantMap φ)
