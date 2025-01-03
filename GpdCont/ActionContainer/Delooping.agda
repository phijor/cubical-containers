{-# OPTIONS --lossy-unification #-}
module GpdCont.ActionContainer.Delooping where

open import GpdCont.Prelude
open import GpdCont.ActionContainer.Base using (ActionContainer)
import      GpdCont.ActionContainer.Morphism as ActionContainerMorphism
open import GpdCont.GroupAction.AssociatedBundle using (associatedBundle ; associatedBundleMap)
open import GpdCont.SymmetricContainer.Base using (SymmetricContainer ; mkSymmetricContainer)
import      GpdCont.SymmetricContainer.Morphism as Symm
import      GpdCont.Delooping

open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base

module Container {ℓ} (F : ActionContainer ℓ) where
  private
    module F = ActionContainer F

  open module 𝔹 {s : F.Shape} = GpdCont.Delooping (F.SymmGroup s) hiding (𝔹) public

  𝔹Symm : (s : F.Shape) → Type ℓ
  𝔹Symm s = 𝔹.𝔹 {s = s}

  DeloopingShape : hGroupoid ℓ
  DeloopingShape .fst = Σ[ s ∈ F.Shape ] 𝔹Symm s
  DeloopingShape .snd = isGroupoidΣ (isSet→isGroupoid F.is-set-shape) λ s → 𝔹.isGroupoid𝔹

  DeloopingPos : ⟨ DeloopingShape ⟩ → hSet ℓ
  DeloopingPos = uncurry λ s → associatedBundle (F.symmAction s)

  Delooping : SymmetricContainer ℓ
  Delooping = mkSymmetricContainer DeloopingShape DeloopingPos

module Morphism {ℓ} {F G : ActionContainer ℓ} (α : ActionContainerMorphism.Morphism F G) where
  open import GpdCont.Delooping.Map using (map)
  open ActionContainerMorphism

  private
    module F = ActionContainer F
    module G = ActionContainer G
    module α = Morphism α

  shape-mor : ⟨ Container.DeloopingShape F ⟩ → ⟨ Container.DeloopingShape G ⟩
  shape-mor (s , x) .fst = α.shape-map s
  shape-mor (s , x) .snd = map (α.symm-hom s) x

  pos-mor : ∀ s* → ⟨ Container.DeloopingPos G (shape-mor s*) ⟩ → ⟨ Container.DeloopingPos F s* ⟩
  pos-mor = uncurry λ s → associatedBundleMap
    (F.symmAction s) (G.symmAction (α.shape-map s))
    (α.symm-hom s)
    (α.pos-map s)
    (α.is-equivariant-pos-map' s)

  Delooping : Symm.Morphism (Container.Delooping F) (Container.Delooping G)
  Delooping .Symm.Morphism.shape-map = shape-mor
  Delooping .Symm.Morphism.pos-map = pos-mor

module Functor (ℓ : Level) where
  open import GpdCont.ActionContainer.Category using (Act)
  open import GpdCont.SymmetricContainer.WildCat using (SymmContWildCat ; hoSymmCont)
  open import GpdCont.WildCat.HomotopyCategory using (ho) renaming (module Notation to HoNotation)
  
  open import Cubical.Categories.Category.Base
  open import Cubical.Categories.Functor.Base
  open import Cubical.WildCat.Base hiding (_[_,_])

  private
    module SymmContWild = WildCat (SymmContWildCat ℓ)

    module hoSymmCont where
      open Category (hoSymmCont ℓ) public
      open HoNotation (SymmContWildCat ℓ) using (trunc-hom) public

      trunc-path : ∀ {F G} {f g : SymmContWild.Hom[ F , G ]} → f ≡ g → trunc-hom f ≡ trunc-hom g
      trunc-path = cong trunc-hom

    module Act = Category (Act {ℓ})

  Delooping₀ = Container.Delooping

  Delooping₁ : ∀ {F G : ActionContainer ℓ} → ActionContainerMorphism.Morphism F G → (hoSymmCont ℓ) [ Container.Delooping F , Container.Delooping G ]
  Delooping₁ = hoSymmCont.trunc-hom ∘ Morphism.Delooping


  Delooping : Functor (Act {ℓ}) (hoSymmCont ℓ)
  Delooping .Functor.F-ob = Delooping₀
  Delooping .Functor.F-hom = Delooping₁
  Delooping .Functor.F-id {x = F} = hoSymmCont.trunc-path (Symm.Morphism≡ {G = Delooping₀ F} {H = Delooping₀ F} shape-id pos-id) where
    module F = ActionContainer F
    module 𝔹F = Container F

    shape-id : Morphism.shape-mor (Act.id {F}) ≡ id ⟨ Container.DeloopingShape F ⟩
    shape-id = funExt $ uncurry goal where
      module _ (s : F.Shape) where
        is-set-shape-mor-path : (x : Container.𝔹Symm F s) → isSet (Morphism.shape-mor Act.id (s , x) ≡ (s , x))
        is-set-shape-mor-path x = str 𝔹F.DeloopingShape _ (s , x)

        goal : (x : 𝔹F.𝔹Symm s) → Morphism.shape-mor Act.id (s , x) ≡ (s , x)
        goal = 𝔹F.elimSet is-set-shape-mor-path refl λ g i j → s , 𝔹F.loop g i

    pos-id : (s* : ⟨ 𝔹F.DeloopingShape ⟩) → PathP (λ i → ⟨ 𝔹F.DeloopingPos (shape-id i s*) ⟩ → ⟨ 𝔹F.DeloopingPos s* ⟩) (Morphism.pos-mor Act.id s*) (id _)
    pos-id = uncurry pos-id-ext where
      pos-id-ext : (s : F.Shape) (x : 𝔹F.𝔹Symm s) → PathP (λ i → ⟨ 𝔹F.DeloopingPos (shape-id i (s , x)) ⟩ → ⟨ 𝔹F.DeloopingPos (s , x) ⟩) _ _
      pos-id-ext s = 𝔹F.elimProp (λ x → isOfHLevelPathP' 1 (isSetΠ λ _ → str (𝔹F.DeloopingPos (s , x))) _ _) refl
  Delooping .Functor.F-seq {x = F} {y = G} {z = H} f g = hoSymmCont.trunc-path (Symm.Morphism≡ {G = Delooping₀ F} {H = Delooping₀ H} shape-seq pos-seq) where
    module F = ActionContainer F
    module H = ActionContainer H
    module 𝔹F = Container F
    module 𝔹H = Container H
    module f⋆g = ActionContainerMorphism.Morphism (f Act.⋆ g)

    shape-seq : Morphism.shape-mor (f Act.⋆ g) ≡ Symm.Morphism.shape-map (Morphism.Delooping f SymmContWild.⋆ Morphism.Delooping g)
    shape-seq = funExt $ uncurry λ s → 𝔹F.elimSet (λ _ → str 𝔹H.DeloopingShape _ _) refl λ g i j → f⋆g.shape-map s , 𝔹H.loop (f⋆g.symm-map s g) i

    pos-seq : (s* : ⟨ 𝔹F.DeloopingShape ⟩) → PathP _ _ _
    pos-seq = uncurry λ s → 𝔹F.elimProp (λ x → isOfHLevelPathP' 1 (isSetΠ λ _ → str (𝔹F.DeloopingPos (s , x))) _ _) refl
