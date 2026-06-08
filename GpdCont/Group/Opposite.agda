module GpdCont.Group.Opposite where

open import GpdCont.Prelude

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.Morphisms

module _ {ℓ} {G : Type ℓ} (G* : GroupStr G) where
  private module G = GroupStr G*

  opaque
    isGroupOppositeStr : IsGroup G.1g (flip G._·_) G.inv
    isGroupOppositeStr = makeIsGroup
      G.is-set
      (λ g h k → sym $ G.·Assoc k h g)
      G.·IdL G.·IdR
      G.·InvL G.·InvR

  oppositeStr : GroupStr G
  oppositeStr .GroupStr.1g = G.1g
  oppositeStr .GroupStr._·_ = flip G._·_
  oppositeStr .GroupStr.inv = G.inv
  oppositeStr .GroupStr.isGroup = isGroupOppositeStr

_ᵒᵖ : ∀ {ℓ} (G : Group ℓ) → Group ℓ
(G ᵒᵖ) .fst = ⟨ G ⟩
(G ᵒᵖ) .snd = oppositeStr (str G)

unop-hom : ∀ {ℓ} (G : Group ℓ) → GroupHom (G ᵒᵖ) G
unop-hom G = inv where
  module G = GroupStr (str G)
  open GroupTheory G

  inv : GroupHom (G ᵒᵖ) G
  inv .fst = G.inv
  inv .snd .IsGroupHom.pres· g h = invDistr h g
  inv .snd .IsGroupHom.pres1 = inv1g
  inv .snd .IsGroupHom.presinv g = refl
