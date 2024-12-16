open import GpdCont.Prelude

open import Cubical.Categories.Category.Base

module GpdCont.Categories.Diagonal {ℓo ℓh} (C : Category ℓo ℓh) (ℓ : Level) where

open import GpdCont.HomotopySet as HSet
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable
private
  module C where
    open Category C public

ΠC : (K : hSet ℓ) → Category _ _
ΠC K .Category.ob = ⟨ K ⟩ → C.ob
ΠC K .Category.Hom[_,_] x y = ∀ k → C.Hom[ x k , y k ]
ΠC K .Category.id k = C.id
ΠC K .Category._⋆_ f g = λ k → f k C.⋆ g k
ΠC K .Category.⋆IdL f = funExt $ C.⋆IdL ∘ f
ΠC K .Category.⋆IdR f = funExt $ C.⋆IdR ∘ f
ΠC K .Category.⋆Assoc f g h = funExt λ k → C.⋆Assoc (f k) (g k) (h k)
ΠC K .Category.isSetHom = isSetΠ λ k → C.isSetHom

Δ : (K : hSet ℓ) → Functor C (ΠC K)
Δ K = ΔK where
  ΔK : Functor _ _
  ΔK .Functor.F-ob c = const c
  ΔK .Functor.F-hom f = const f
  ΔK .Functor.F-id = refl
  ΔK .Functor.F-seq _ _ = refl
