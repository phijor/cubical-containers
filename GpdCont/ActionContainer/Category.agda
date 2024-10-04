module GpdCont.ActionContainer.Category where

open import GpdCont.Prelude
open import GpdCont.HomotopySet using (hSet≡)
open import GpdCont.Univalence using (ua→)
open import GpdCont.DisplayedCategories using (Fam ; Famᴰ ; constᴰ ; FamHom≡ ; Fam≡)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Category using (GroupAction ; GroupActionHom≡)
open import GpdCont.ActionContainer.Abstract
open import GpdCont.ActionContainer.Morphism hiding (mkMorphism-syntax)
open import GpdCont.ActionContainer.Transformation

open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.Data.Sigma as Sigma using ()

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath using (uaGroup)

open import Cubical.Categories.Category.Base using (Category ; _[_,_])
open import Cubical.Categories.Functor as FunctorM using (Functor ; _⟅_⟆ ; _⟪_⟫) renaming (𝟙⟨_⟩ to idFunctor ; _∘F_ to _∘ꟳ_)
open import Cubical.Categories.NaturalTransformation as NT using (_≅ᶜ_ ; NatIso ; NatTrans)
open import Cubical.Categories.Equivalence using (_≃ᶜ_ ; WeakInverse)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Constructions.TotalCategory using (∫C)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Instances.Terminal using (TerminalCategory)

module _ {ℓ} where
  idAct : (C : ActionContainer ℓ) → Morphism C C
  idAct C = ( id _ ▷ ((λ s → id _) , λ s g → refl) ◁ λ s → idGroupHom ) where
    open GpdCont.ActionContainer.Morphism C C using (mkMorphism-syntax)

  compAct' : ∀ {C D E : ActionContainer ℓ} → Morphism C D → Morphism D E → Morphism C E
  compAct' {C} {E} f g = f⋆g where
    module f = Morphism f
    module g = Morphism g

    f⋆g : Morphism C E
    f⋆g = mkMorphismBundled _ _
      (f.shape-map ⋆ g.shape-map)
      (λ s → compGroupHom (f.symm-hom s) (g.symm-hom (f.shape-map s)))
      ({! !} , {! !})

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

  open Functor

  FamGroupAction = Fam ℓ (GroupAction ℓ)
  module FamGroupAction = Category FamGroupAction

  Act→FamGroupAction : Functor Act FamGroupAction
  Act→FamGroupAction .F-ob C = C.ShapeSet , λ s → (C.SymmGroup s , C.PosSet s) , C.symmAction s where
    module C = ActionContainer C
  Act→FamGroupAction .F-hom f = f.shape-map , λ s → (f.symm-hom s , f.pos-map s) , f.is-equivariant-pos-map s where
    module f = Morphism f
  Act→FamGroupAction .F-id = refl
  Act→FamGroupAction .F-seq f g = FamHom≡ _ _ refl λ j → GroupActionHom≡ refl

  FamGroupAction→Act : Functor FamGroupAction Act
  FamGroupAction→Act .F-ob (S , σ*) = mkActionContainer S P G σ where
    P = snd ∘ fst ∘ σ*
    G = fst ∘ fst ∘ σ*
    σ = snd ∘ σ*
  FamGroupAction→Act .F-hom (u , φ*) = mkMorphismBundled _ _ u φ (f , is-equivariant) where
    φ = fst ∘ fst ∘ φ*
    f = snd ∘ fst ∘ φ*
    is-equivariant = snd ∘ φ*
  FamGroupAction→Act .F-id = refl
  FamGroupAction→Act .F-seq f g = Morphism≡ _ _ refl refl refl

  theorem : Act ≃ᶜ Fam ℓ (GroupAction ℓ)
  theorem ._≃ᶜ_.func = Act→FamGroupAction
  theorem ._≃ᶜ_.isEquiv = PT.∣ weak-inv ∣₁ where
    to = Act→FamGroupAction
    from = FamGroupAction→Act

    to∘from : Functor FamGroupAction FamGroupAction
    to∘from = to ∘ꟳ from

    -- Action of morphisms of the composition of to and from, with explicit annotations for domain and codomain to help unification.
    to∘from[_,_]⟪_⟫ : (σ τ : FamGroupAction.ob) → FamGroupAction [ σ , τ ] → FamGroupAction [ to∘from ⟅ σ ⟆ , to∘from ⟅ τ ⟆ ]
    to∘from[_,_]⟪_⟫ σ τ = to∘from .Functor.F-hom {x = σ} {y = τ}

    open NatTrans
    open NatIso

    module η where opaque
      ob : ∀ C → C ≡ (from ∘ꟳ to) ⟅ C ⟆
      ob C = ActionContainer≡ refl refl g-path refl where
        module C = ActionContainer C
        module C′ = ActionContainer ((from ∘ꟳ to) ⟅ C ⟆)

        g-path : C.SymmGroup ≡ C′.SymmGroup
        g-path i s .fst = C.Symm s
        g-path i s .snd .GroupStr.1g = C.symm-id
        g-path i s .snd .GroupStr._·_ = C._·_
        g-path i s .snd .GroupStr.inv = C.symm-inv
        g-path i s .snd .GroupStr.isGroup = isProp→PathP {B = λ i → IsGroup _ _ _} (λ i → isPropIsGroup _ _ _)
          (GroupStr.isGroup (C.symm-group-str s))
          (GroupStr.isGroup (C′.symm-group-str s))
          i

      hom : ∀ {C} {D} (f : Act [ C , D ]) → PathP (λ i → Act [ ob C i , ob D i ]) f ((from ∘ꟳ to) ⟪ f ⟫)
      hom {C} {D} f i = mkMorphism _ _ f.shape-map f.pos-map f.symm-map f.is-equivariant-pos-map is-group-hom-symm-mapᵢ where
        module f = Morphism f

        is-group-hom-symm-mapᵢ : isSymmGroupHom (ob C i) (ob D i) f.symm-map
        is-group-hom-symm-mapᵢ =
          isProp→PathP {B = λ i → isSymmGroupHom (ob C i) (ob D i) f.symm-map}
            (λ i → isPropIsSymmGroupHom (ob C i) (ob D i))
            f.is-group-hom-symm-map
            f.is-group-hom-symm-map
            i

      functor-path : idFunctor Act ≡ from ∘ꟳ to
      functor-path = FunctorM.Functor≡ ob hom

    η : idFunctor Act ≅ᶜ from ∘ꟳ to
    η = NT.pathToNatIso η.functor-path

    module ε where
      ob : (σ@(J , σⱼ) : FamGroupAction.ob) → (to ∘ꟳ from) ⟅ (J , σⱼ) ⟆ ≡ (J , σⱼ)
      ob (J , σⱼ) = Fam≡ _ (GroupAction _) (hSet≡ $ refl′ ⟨ J ⟩) refl

      hom : ∀ (σ@(J , σⱼ) τ@(K , τₖ) : FamGroupAction.ob) (f : FamGroupAction [ σ , τ ]) → PathP (λ i → FamGroupAction [ ob σ i , ob τ i ]) to∘from[ σ , τ ]⟪ f ⟫ f
      hom _ _ (f , φⱼ) i = f , λ j → φⱼ j

    ε : to ∘ꟳ from ≅ᶜ idFunctor FamGroupAction
    ε = NT.pathToNatIso (FunctorM.Functor≡ ε.ob λ {σ} {τ} → ε.hom σ τ)

    weak-inv : WeakInverse Act→FamGroupAction
    weak-inv .WeakInverse.invFunc = FamGroupAction→Act
    weak-inv .WeakInverse.η = η
    weak-inv .WeakInverse.ε = ε
