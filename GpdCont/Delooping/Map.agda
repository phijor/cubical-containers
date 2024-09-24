module GpdCont.Delooping.Map where

open import GpdCont.Prelude

import GpdCont.Delooping as Delooping

import Cubical.Foundations.Path as Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

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

module _
  {φ*@(φ , _) ψ*@(ψ , _) : GroupHom G H}
  (open GroupStr (str H) using (_·_))
  (h : ⟨ H ⟩)
  (h-conj : ∀ g → (φ g · h) ≡ (h · ψ g))
  where
  private
    module BG = Delooping ⟨ G ⟩ (str G)
    module BH = Delooping ⟨ H ⟩ (str H)
    module H = GroupStr (str H)

    map-ext-⋆ : BH.⋆ ≡ BH.⋆
    map-ext-⋆ = BH.loop h

    map-ext-loop : ∀ g → Square (BH.loop h) (BH.loop h) (BH.loop (φ g)) (BH.loop (ψ g))
    map-ext-loop g = Path.compPath→Square $
      BH.loop (φ g) ∙ BH.loop h ≡⟨ BH.loop-∙ (φ g) h ⟩
      BH.loop (φ g H.· h)       ≡⟨ cong BH.loop (h-conj g) ⟩
      BH.loop (h H.· ψ g)       ≡⟨ sym $ BH.loop-∙ h (ψ g) ⟩
      BH.loop h ∙ BH.loop (ψ g) ∎

  map≡-ext : (x : 𝔹 G) → map φ* x ≡ map ψ* x
  map≡-ext = BG.elimSet (λ x → BH.isGroupoid𝔹 (map φ* x) (map ψ* x)) map-ext-⋆ map-ext-loop

  map≡ : map φ* ≡ map ψ*
  map≡ = funExt map≡-ext

mapEquiv' : (G H : Group ℓ) → (f g : 𝔹 G → 𝔹 H) → (f ≡ g) ≃ {! !}
mapEquiv' G H f g =
  (f ≡ g) ≃⟨ {! !} ⟩
  ((x : 𝔹 G) → f x ≡ g x) ≃⟨ invEquiv (Delooping.elimSetEquiv ⟨ G ⟩ (str G) λ x → BH.isGroupoid𝔹 (f x) (g x)) ⟩
  (Σ[ q₀ ∈ (f BG.⋆ ≡ g BG.⋆) ] (∀ k → PathP (λ i → f (BG.loop k i) ≡ g (BG.loop k i)) q₀ q₀)) ≃⟨ ? ⟩
  {! !} ≃∎
  where
  module BG = Delooping ⟨ G ⟩ (str G)
  module BH = Delooping ⟨ H ⟩ (str H)
mapEquivTrunc : (G H : Group ℓ) → (GroupHom G H) ≃ ∥ (𝔹 G → 𝔹 H) ∥₂
mapEquivTrunc G H =
  {! !} ≃⟨ {! !} ⟩
  ∥ Σ[ y₀ ∈ 𝔹 H ] (Σ[ φ ∈ (⟨ G ⟩ → y₀ ≡ y₀) ] (∀ g h → compSquareFiller (φ g) (φ h) (φ $ (G .snd GroupStr.· g) h))) ∥₂ ≃⟨ cong≃ ∥_∥₂ $ Delooping.recEquiv _ _ {X = _ , BH.isGroupoid𝔹} ⟩
  ∥ (𝔹 G → 𝔹 H) ∥₂ ≃∎ where

  module BG = Delooping ⟨ G ⟩ (str G)
  module BH = Delooping ⟨ H ⟩ (str H)

mapIso : (G H : Group ℓ) → Iso (GroupHom G H) (𝔹 G → 𝔹 H)
mapIso G H = go where
  -- {! !} ≃⟨ {! !} ⟩
  -- Σ[ y₀ ∈ BH.𝔹 ] (Σ[ φ ∈ (G .fst → y₀ ≡ y₀) ] (∀ g h → compSquareFiller (φ g) (φ h) (φ $ (G .snd GroupStr.· g) h))) ≃⟨ Delooping.recEquiv _ _ {X = _ , BH.isGroupoid𝔹} ⟩
  -- (𝔹 G → 𝔹 H) ≃∎ where

  module BG = Delooping ⟨ G ⟩ (str G)
  module BH = Delooping ⟨ H ⟩ (str H)

  go : Iso _ _
  go .Iso.fun = map
  go .Iso.inv f = (λ g → {!  cong f $ BG.loop g !}) , {! !}
  go .Iso.rightInv = {! !}
  go .Iso.leftInv = {! !}
