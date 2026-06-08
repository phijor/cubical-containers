open import GpdCont.Prelude renaming (_×_ to _×ᵗ_)

open import Cubical.Categories.Category.Base

module GpdCont.Categories.Products {ℓo ℓh} (C : Category ℓo ℓh) (ℓ : Level) where

open import GpdCont.HomotopySet as HSet
import      GpdCont.Categories.Diagonal as Diagonal

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable using (UniversalElement) public
open import Cubical.Categories.Limits.BinProduct.More

private
  module C where
    open Category C public
    open Diagonal C ℓ public


Product : (K : hSet ℓ) → (c : ⟨ K ⟩ → C.ob) → Type _
Product K = RightAdjointAt (C.Δ K)

Products : Type _
Products = ∀ K → RightAdjoint (C.Δ K)

module NotationAt (K : hSet ℓ) (c : ⟨ K ⟩ → C.ob) (ip : Product K c) where
  open UniversalElement ip

  Π : C.ob
  Π = vertex

  π : (k : ⟨ K ⟩) → C.Hom[ Π , c k ]
  π = element

  module _ (x : C.ob) where
    is-universal : isEquiv (λ f k → f C.⋆ π k)
    is-universal = universal x

    univ-equiv : C.Hom[ x , Π ] ≃ (∀ k → C.Hom[ x , c k ])
    univ-equiv = _ , is-universal

    univ-iso : Iso C.Hom[ x , Π ] (∀ k → C.Hom[ x , c k ])
    univ-iso = equivToIso univ-equiv

module Notation (ip : Products) where
  module _ K (c : ⟨ K ⟩ → C.ob) where open NotationAt K c (ip K c) public

  private
    BoolSet : hSet ℓ
    BoolSet = (Bool* , isOfHLevelLift 2 isSetBool)

    case : C.ob → C.ob → ⟨ BoolSet ⟩ → C.ob
    case x y (lift false) = y
    case x y (lift true) = x

    bool-elim-equiv : ∀ {ℓ'} {B : ⟨ BoolSet ⟩ → Type ℓ'} → (∀ k → B k) ≃ (B true*) ×ᵗ (B false*)
    bool-elim-equiv = isoToEquiv λ where
      .Iso.fun φ → φ _ , φ _
      .Iso.inv (x , y) → λ { (lift true) → x ; (lift false) → y }
      .Iso.ret φ → funExt λ { (lift true) → refl ; (lift false) → refl }
      .Iso.sec (x , y) → refl

  terminal : C.ob
  terminal = Π (EmptySet ℓ) λ ()

  _×_ : C.ob → C.ob → C.ob
  _×_ x y = Π BoolSet (case x y)

  π₁ : ∀ {x y} → C.Hom[ x × y , x ]
  π₁ = π _ _ (lift true)

  π₂ : ∀ {x y} → C.Hom[ x × y , y ]
  π₂ = π _ _ (lift false)

  binProducts : BinProducts C
  binProducts = bp where
    bp : ∀ x,y → BinProduct C x,y
    bp (x , y) .UniversalElement.vertex = x × y
    bp (x , y) .UniversalElement.element .fst = π₁
    bp (x , y) .UniversalElement.element .snd = π₂
    bp (x , y) .UniversalElement.universal z .equiv-proof (f₁ , f₂) =
      isOfHLevelRespectEquiv 0 hom-equiv (equivIsEquiv (univ-equiv BoolSet _ _) .equiv-proof fᵇ)
      where
      open import Cubical.Functions.FunExtEquiv

      fᵇ : (k : ⟨ BoolSet ⟩) → C.Hom[ z , case x y k ]
      fᵇ (lift false) = f₂
      fᵇ (lift true) = f₁

      hom-equiv : fiber (equivFun (univ-equiv BoolSet (case x y) z)) fᵇ ≃ (Σ[ f* ∈ C.Hom[ z , x × y ] ] (f* C.⋆ π₁ , f* C.⋆ π₂) ≡ (f₁ , f₂))
      hom-equiv = Σ-cong-equiv-snd λ (f* : C.Hom[ z , x × y ]) →
        equivFun (univ-equiv (Bool* , isOfHLevelLift 2 isSetBool) (case x y) z) f* ≡ fᵇ
          ≃⟨ invEquiv funExtEquiv ⟩
        (∀ k → _ ≡ fᵇ k)
          ≃⟨ bool-elim-equiv ⟩
        (f* C.⋆ π₁ ≡ f₁) ×ᵗ (f* C.⋆ π₂ ≡ f₂)
          ≃⟨ ΣPathP≃PathPΣ ⟩
        (f* C.⋆ π₁ , f* C.⋆ π₂) ≡ (f₁ , f₂)
          ≃∎
