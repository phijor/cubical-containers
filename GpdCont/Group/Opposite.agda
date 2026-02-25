module GpdCont.Group.Opposite where

open import GpdCont.Prelude

open import Cubical.Algebra.Group.Base

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
