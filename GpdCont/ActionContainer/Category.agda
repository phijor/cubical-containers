module GpdCont.ActionContainer.Category where

open import GpdCont.Prelude
open import GpdCont.GroupAction.Base
open import GpdCont.ActionContainer.Abstract
open import GpdCont.ActionContainer.Morphism hiding (mkMorphism-syntax)
open import GpdCont.ActionContainer.Transformation

open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Constructions.TotalCategory using (∫C)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Instances.Terminal using (TerminalCategory)

module _ {ℓ} where
  private
    term : Functor (SET ℓ) TerminalCategory
    term .Functor.F-ob _ = _
    term .Functor.F-hom _ = refl
    term .Functor.F-id = refl
    term .Functor.F-seq _ _ = {! !}

  GroupActionCategory : Category _ _
  GroupActionCategory .Category.ob = Σ[ G ∈ Group ℓ ] Σ[ X ∈ hSet ℓ ] Action G X
  GroupActionCategory .Category.Hom[_,_] = {! !}
  GroupActionCategory .Category.id = {! !}
  GroupActionCategory .Category._⋆_ = {! !}
  GroupActionCategory .Category.⋆IdL = {! !}
  GroupActionCategory .Category.⋆IdR = {! !}
  GroupActionCategory .Category.⋆Assoc = {! !}
  GroupActionCategory .Category.isSetHom = {! !}

  AC : Categoryᴰ (SET ℓ) _ _
  AC = reindex (Category→DispOverTerminal GroupActionCategory) term

  AC′ : Categoryᴰ (SET ℓ) _ _
  AC′ = reindex {! !} {! !}

  _ = {! AC .Categoryᴰ.ob[_] ? !}

  ∫AC : Category _ _
  ∫AC = ∫C AC

  idAct : (C : ActionContainer ℓ) → Morphism C C
  idAct C = ( id _ ▷ ((λ s → id _) , λ s g → refl) ◁ λ s → idGroupHom ) where
    open GpdCont.ActionContainer.Morphism C C using (mkMorphism-syntax)

  compAct : ∀ {C D E : ActionContainer ℓ} → Morphism C D → Morphism D E → Morphism C E
  compAct {C} {E} f g = ( (f .shape-map ⋆ g .shape-map) ▷ ((λ _ → g .pos-map _ ⋆ f .pos-map _) , {! !}) ◁ λ _ → compGroupHom (Morphism.symm-hom f _) (Morphism.symm-hom g _)) where
    open Morphism
    open Morphismᴰ
    open GpdCont.ActionContainer.Morphism C E using (mkMorphism-syntax)

  Act : Category _ _
  Act .Category.ob = ActionContainer ℓ
  Act .Category.Hom[_,_] = Morphism
  Act .Category.id {x = C} = idAct C
  Act .Category._⋆_ = compAct
  Act .Category.⋆IdL = {! !}
  Act .Category.⋆IdR = {! !}
  Act .Category.⋆Assoc = {! !}
  Act .Category.isSetHom = isSetMorphism _ _

  _ : (∫AC .Category.ob) ≡ (Σ[ S ∈ hSet _ ] Σ[ G ∈ Group _ ] Σ[ X ∈ hSet ℓ ] (Action G X))
  _ = refl

  module _ (C D : ActionContainer ℓ) where
    ActLocal : Category _ _
    ActLocal .Category.ob = Morphism C D
    ActLocal .Category.Hom[_,_] = TransformationP
    ActLocal .Category.id = idTransformationP _
    ActLocal .Category._⋆_ = vcompTransformationP
    ActLocal .Category.⋆IdL = {! !}
    ActLocal .Category.⋆IdR = {! !}
    ActLocal .Category.⋆Assoc = {! !}
    ActLocal .Category.isSetHom = isSetTransformationP

  -- AC .Categoryᴰ.ob[_] (S , is-set-S) = Σ[ P ∈ (S → hSet ℓ) ] Σ[ G ∈ (S → Group ℓ) ] ∀ s → Action (G s) (P s)
  -- AC .Categoryᴰ.Hom[_][_,_] f = {! !}
  -- AC .Categoryᴰ.idᴰ = {! !}
  -- AC .Categoryᴰ._⋆ᴰ_ = {! !}
  -- AC .Categoryᴰ.⋆IdLᴰ = {! !}
  -- AC .Categoryᴰ.⋆IdRᴰ = {! !}
  -- AC .Categoryᴰ.⋆Assocᴰ = {! !}
  -- AC .Categoryᴰ.isSetHomᴰ = {! !}
