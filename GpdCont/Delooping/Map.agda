module GpdCont.Delooping.Map where

open import GpdCont.Prelude

import GpdCont.Delooping as Delooping

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom)

private
  variable
    ℓ : Level
    G H : Group ℓ

  𝔹 : (G : Group ℓ) → Type ℓ
  𝔹 = uncurry Delooping.𝔹

map : (φ : GroupHom G H) → 𝔹 G → 𝔹 H
map {G} {H} (φ , is-hom-φ) = Delooping.rec ⟨ G ⟩ (str G) Delooping.isGroupoid𝔹 Delooping.⋆ φ′ φ′-comm where
  module G = GroupStr (str G)
  module H = GroupStr (str H)
  
  module φ = IsGroupHom is-hom-φ

  φ′ : ⟨ G ⟩ → Delooping.⋆ ≡ Delooping.⋆
  φ′ g = Delooping.loop (φ g)

  φ′-comm : ∀ g g′ → compSquareFiller (φ′ g) (φ′ g′) (φ′ (g G.· g′))
  φ′-comm g g′ = subst (compSquareFiller _ _) (cong Delooping.loop $ sym (φ.pres· g g′)) (Delooping.loop-comp (φ g) (φ g′))

map-id : (G : Group ℓ) → map (idGroupHom {G = G}) ≡ id (𝔹 G)
map-id G = funExt (Delooping.elimSet ⟨ G ⟩  (str G) (λ _ → Delooping.isGroupoid𝔹 _ _) refl λ g i j → Delooping.loop g i)
