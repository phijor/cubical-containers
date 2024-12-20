open import GpdCont.Prelude renaming (_×_ to _×ᵗ_)

open import Cubical.Categories.Category.Base

module GpdCont.Categories.Products {ℓo ℓh} (C : Category ℓo ℓh) (ℓ : Level) where

open import GpdCont.HomotopySet as HSet
import      GpdCont.Categories.Diagonal as Diagonal

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable using (UniversalElement) public
open import Cubical.Categories.Limits.BinProduct using (BinProduct ; BinProducts)
open import Cubical.Categories.Limits.BinProduct.More
  using (BinProduct' ; BinProducts' ; BinProducts'ToBinProducts ; BinProduct'ToBinProduct)
  renaming (module Notation to BinProductNotation)

private
  module C where
    open Category C public
    open Diagonal C ℓ public


Product : (K : hSet ℓ) → (c : ⟨ K ⟩ → C.ob) → Type _
Product K = RightAdjointAt' _ _ (C.Δ K)

Products : Type _
Products = ∀ K → RightAdjoint' _ _ (C.Δ K)

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

module ToBinProduct (ip : Products) where
  open import GpdCont.Bool
  open module Foo K (c : ⟨ K ⟩ → C.ob) = NotationAt K c (ip K c)

  _×_ : C.ob → C.ob → C.ob
  _×_ x y = Π BoolSet (bool-elim x y)

  ×-π' : (x y : C.ob) → (k : ⟨ BoolSet ⟩) → C.Hom[ x × y , bool-elim x y k ]
  ×-π' x y = π BoolSet (bool-elim x y)

  ×-π₁ : (x y : C.ob) → C.Hom[ x × y , x ]
  ×-π₁ x y = ×-π' x y true*

  ×-π₂ : (x y : C.ob) → C.Hom[ x × y , y ]
  ×-π₂ x y = ×-π' x y false*

  ×-π : (x y : C.ob) → C.Hom[ x × y , x ] ×ᵗ C.Hom[ x × y , y ]
  ×-π x y = bool-unelim {A = λ b → C.Hom[ x × y , bool-elim x y b ]} (×-π' x y)

  ×-univ-equiv' : (x y z : C.ob) → C.Hom[ z , x × y ] ≃ ∀ b → C.Hom[ z , bool-elim x y b ]
  ×-univ-equiv' x y = univ-equiv BoolSet (bool-elim x y)

  ×-univ-equiv : (x y z : C.ob) → C.Hom[ z , x × y ] ≃ (C.Hom[ z , x ] ×ᵗ C.Hom[ z , y ])
  ×-univ-equiv x y z = ×-univ-equiv' x y z ∙ₑ bool-unelim-equiv

  binProduct' : (x y : C.ob) → BinProduct' C (x , y)
  binProduct' x y .UniversalElement.vertex = x × y
  binProduct' x y .UniversalElement.element = ×-π x y
  binProduct' x y .UniversalElement.universal z = equivIsEquiv (×-univ-equiv x y z)

  binProduct : (x y : C.ob) → BinProduct C x y
  binProduct x y = BinProduct'ToBinProduct C (binProduct' x y)

Products→BinProducts' : Products → BinProducts' C
Products→BinProducts' p (x , y) = ToBinProduct.binProduct' p x y

Products→BinProducts : Products → BinProducts C
Products→BinProducts = BinProducts'ToBinProducts C ∘ Products→BinProducts'

module Notation (ip : Products) where
  open import GpdCont.Bool

  module _ K (c : ⟨ K ⟩ → C.ob) where open NotationAt K c (ip K c) public

  terminal : C.ob
  terminal = Π (EmptySet ℓ) λ ()

  open BinProductNotation _ (ToBinProduct.binProduct ip) public
