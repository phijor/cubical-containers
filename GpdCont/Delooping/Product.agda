module GpdCont.Delooping.Product where

open import GpdCont.Prelude
open import GpdCont.Delooping as Delooping using (𝔹 ; isGroupoid𝔹 ; ⋆ ; loop ; loop-comp)
open import GpdCont.Delooping.Map as Map using (map)
open import GpdCont.Group.DirProd using (module DirProd) renaming (DirProd to _⊗_)
open import GpdCont.Group.Pi using (ΠGroup)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base

private
  variable
    ℓ : Level

module _ {ℓG ℓH} (G : Group ℓG) (H : Group ℓH) where
  private
    module G = GroupStr (str G)
    module H = GroupStr (str H)

  DeloopingFst : 𝔹 (G ⊗ H) → 𝔹 G
  DeloopingFst = map (DirProd.fstHom G H)

  DeloopingSnd : 𝔹 (G ⊗ H) → 𝔹 H
  DeloopingSnd = map (DirProd.sndHom G H)

  DeloopingDirProdIso : Iso (𝔹 (G ⊗ H)) ((𝔹 G) × (𝔹 H))
  DeloopingDirProdIso .Iso.fun = Delooping.rec (G ⊗ H) (isGroupoid× isGroupoid𝔹 isGroupoid𝔹)
    (⋆ , ⋆)
    (λ { (g , h) i → loop g i , loop h i })
    λ { (g , h) (g′ , h′) i j → loop-comp g g′ i j , loop-comp h h′ i j }
  DeloopingDirProdIso .Iso.inv = uncurry $ Delooping.rec G (isGroupoidΠ λ _ → isGroupoid𝔹)
    (Delooping.rec H isGroupoid𝔹 (⋆) (λ h → loop (G.1g , h)) λ { h h′ i j → {! loop-comp (G.1g , h) (G.1g , h′) i j !} })
    (λ g → funExt (Delooping.elimSet H (λ y → isGroupoid𝔹 _ _) (loop (g , H.1g)) {! !}))
    λ { g g′ → funExtSquare (Delooping.elimProp H {! !} λ { i j → loop-comp (g , H.1g) (g′ , H.1g) i {! !} }) }
  DeloopingDirProdIso .Iso.rightInv = uncurry {! !}
  DeloopingDirProdIso .Iso.leftInv = Delooping.elimSet (G ⊗ H) {! !} refl {! !}

  DeloopingDirProdEquiv : 𝔹 (G ⊗ H) ≃ (𝔹 G) × (𝔹 H)
  DeloopingDirProdEquiv = {! !}

module _ {ℓ ℓG} {X : Type ℓ} (G : X → Group ℓG) where
  private
    module 𝔹ΠG = Delooping (ΠGroup G)

  𝔹Π→Π𝔹 : 𝔹 (ΠGroup G) → (∀ x → 𝔹 (G x))
  𝔹Π→Π𝔹 = 𝔹ΠG.rec (isGroupoidΠ λ x → isGroupoid𝔹)
    (λ x → ⋆)
    (λ g i x → loop (g x) i)
    (λ g h i j x → loop-comp (g x) (h x) i j)


--     isEquiv-𝔹Π→Π𝔹 : isEquiv 𝔹Π→Π𝔹
--     isEquiv-𝔹Π→Π𝔹 .equiv-proof g = {! !}

--     Π𝔹→𝔹Π : (∀ x → 𝔹 (G x)) → 𝔹 (ΠGroup G)
--     Π𝔹→𝔹Π g = {! !}

--   DeloopingΠIso : Iso (𝔹 (ΠGroup G)) (∀ x → 𝔹 (G x))
--   DeloopingΠIso .Iso.fun = 𝔹Π→Π𝔹
--   DeloopingΠIso .Iso.inv = {! !}
--   DeloopingΠIso .Iso.rightInv = {! !}
--   DeloopingΠIso .Iso.leftInv = {! !}

--   DeloopingΠEquiv : 𝔹 (ΠGroup G) ≃ (∀ x → 𝔹 (G x))
--   DeloopingΠEquiv = {! !}
