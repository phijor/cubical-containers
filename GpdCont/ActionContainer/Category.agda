module GpdCont.ActionContainer.Category where

open import GpdCont.Prelude
open import GpdCont.HomotopySet using (hSet≡)
open import GpdCont.Categories.Family using (Fam ; Famᴰ ; FamHom≡ ; Fam≡)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Category using (GroupAction ; GroupActionHom≡)
open import GpdCont.ActionContainer.Abstract
open import GpdCont.ActionContainer.Morphism hiding (mkMorphism-syntax)
open import GpdCont.QuotientContainer.Base using (QCont)
open import GpdCont.QuotientContainer.Premorphism using (Premorphism ; isReflPremorphismEquiv)
open import GpdCont.QuotientContainer.Morphism
  using (pre-morphism-class ; pre-morphism-eq/)
  renaming (Morphism to QMorphism ; PremorphismEquiv→Morphism≡ to QMorphism≡)
open import GpdCont.QuotientContainer.Category renaming (QCONT to Quot)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
import      Cubical.Functions.Embedding as Embedding
import      Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties using (isPropIsGroup)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom ; compGroupHom)

open import Cubical.Categories.Category.Base using (Category ; _[_,_])
open import Cubical.Categories.Functor as FunctorM using (Functor ; _⟅_⟆ ; _⟪_⟫) renaming (𝟙⟨_⟩ to idFunctor ; _∘F_ to _∘ꟳ_)
open import Cubical.Categories.NaturalTransformation as NT using (_≅ᶜ_ ; NatIso ; NatTrans)
open import Cubical.Categories.Equivalence using (_≃ᶜ_ ; WeakInverse)
open import Cubical.Categories.Constructions.FullSubcategory using (FullSubcategory)

module _ {ℓ} where
  idAct : (C : ActionContainer ℓ) → Morphism C C
  idAct C = ( id _ ▷ ((λ s → id _) , λ s g → refl) ◁ λ s → idGroupHom ) where
    open GpdCont.ActionContainer.Morphism C C using (mkMorphism-syntax)

  compAct : ∀ {C D E : ActionContainer ℓ} → Morphism C D → Morphism D E → Morphism C E
  compAct {C} {D} {E} f g = mkMorphismBundled _ _
      f⋆g-shape
      f⋆g-hom
      (f⋆g-pos , f⋆g-pos-is-eqva) where
    module C = ActionContainer C
    module D = ActionContainer D
    module E = ActionContainer E

    module f = Morphism f
    module g = Morphism g

    f⋆g-shape : C.Shape → E.Shape
    f⋆g-shape = f.shape-map ⋆ g.shape-map

    f⋆g-hom : ∀ s → GroupHom (C.SymmGroup s) (E.SymmGroup _)
    f⋆g-hom s = compGroupHom (f.symm-hom s) (g.symm-hom (f.shape-map s))

    f⋆g-pos : ∀ s → E.Pos _ → C.Pos s
    f⋆g-pos s = f.pos-map s ∘ g.pos-map (f.shape-map s)

    abstract
      f⋆g-pos-is-eqva : isEquivariantPosMap C E f⋆g-pos (fst ∘ f⋆g-hom)
      f⋆g-pos-is-eqva s g =
        equivFun (C.action g) ∘ (f⋆g-pos s) ≡⟨⟩
        equivFun (C.action g) ∘ f.pos-map s ∘ g.pos-map (f.shape-map s) ≡[ i ]⟨ f.is-equivariant-pos-map s g i ∘ g.pos-map _ ⟩
        f.pos-map s ∘ equivFun (D.action _) ∘ g.pos-map (f.shape-map s) ≡[ i ]⟨ f.pos-map s ∘ g.is-equivariant-pos-map (f.shape-map s) (f.symm-map s g) i ⟩
        f⋆g-pos s ∘ (equivFun $ E.action (f⋆g-hom s .fst g)) ∎

  Act : Category _ _
  Act .Category.ob = ActionContainer ℓ
  Act .Category.Hom[_,_] = Morphism
  Act .Category.id {x = C} = idAct C
  Act .Category._⋆_ = compAct
  Act .Category.⋆IdL f = Morphism≡ _ _ refl refl refl
  Act .Category.⋆IdR f = Morphism≡ _ _ refl refl refl
  Act .Category.⋆Assoc f g h = Morphism≡ _ _ refl refl refl
  Act .Category.isSetHom = isSetMorphism _ _

  open Functor

  FamGroupAction = Fam ℓ (GroupAction ℓ)
  module FamGroupAction = Category FamGroupAction

  Act→FamGroupAction : Functor Act FamGroupAction
  Act→FamGroupAction .F-ob C = C.ShapeSet , λ s → (C.SymmGroup s , C.PosSet s) , C.symmAction s where
    module C = ActionContainer C
  Act→FamGroupAction .F-hom f = f.shape-map , λ s → (f.symm-hom s , f.pos-map s) , f.is-equivariant-pos-map s where
    module f = Morphism f
  Act→FamGroupAction .F-id = refl
  Act→FamGroupAction .F-seq {x} {y} {z} f g = FamHom≡ ℓ (GroupAction ℓ)
    {X = Act→FamGroupAction .F-ob x} {Y = Act→FamGroupAction .F-ob z}
    refl
    λ j → GroupActionHom≡ ℓ {Act→FamGroupAction .F-ob x .snd j} {Act→FamGroupAction .F-ob z .snd _} refl


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

  Act≃FamGroupAction : Act ≃ᶜ Fam ℓ (GroupAction ℓ)
  Act≃FamGroupAction ._≃ᶜ_.func = Act→FamGroupAction
  Act≃FamGroupAction ._≃ᶜ_.isEquiv = PT.∣ weak-inv ∣₁ where
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

  isFaithfulActionContainer : ActionContainer ℓ → Type _
  isFaithfulActionContainer C = (s : Shape) → Embedding.hasPropFibers (action {s}) where
    open ActionContainer C

  isPropIsFaitfulActionContainer : ∀ C → isProp (isFaithfulActionContainer C)
  isPropIsFaitfulActionContainer c = isPropΠ λ s → Embedding.hasPropFibersIsProp

  ActFaith : Category _ _
  ActFaith = FullSubcategory Act isFaithfulActionContainer

  private
    module ActFaith = Category ActFaith
    module Quot = Category (Quot ℓ)

  ∣_∣₀ : ActFaith.ob → Quot.ob
  ∣ (C , is-ff) ∣₀ = goal where
    open ActionContainer C

    goal : QCont ℓ
    goal .QCont.Shape = Shape
    goal .QCont.Pos = Pos
    goal .QCont.isSymm = fiber action
    goal .QCont.is-set-shape = is-set-shape
    goal .QCont.is-set-pos = is-set-pos
    goal .QCont.is-prop-symm {s} = is-ff s
    goal .QCont.symm-id s = symm-id , action-pres-1
    goal .QCont.symm-sym σ = λ { (g , p) → symm-inv g , action-pres-inv g ∙ cong invEquiv p }
    goal .QCont.symm-comp σ τ = λ { (g , p) (h , q) → g · h , action-pres-· g h ∙ (cong₂ _∙ₑ_ p q) }

  ∣-∣₁-pre : ∀ C D → (F : ActFaith [ C , D ]) → Premorphism ∣ C ∣₀ ∣ D ∣₀ (F .Morphism.shape-map)
  ∣-∣₁-pre (C , _) (D , _) F = ∣F∣₁-pre where
    module F = Morphism F
    module C = ActionContainer C
    module D = ActionContainer D

    ∣F∣₁-pre : Premorphism _ _ _
    ∣F∣₁-pre .Premorphism.pos-mor = F.pos-map
    ∣F∣₁-pre .Premorphism.symm-pres s (p , g , fib-p) =
      ∃-intro (D.action (F.symm-map s g) , (F.symm-map s g) , refl) $
        equivFun p ∘ F.pos-map s ≡⟨ cong (λ p → equivFun p ∘ _) (sym fib-p) ⟩
        equivFun (C.action g) ∘ F.pos-map s ≡⟨ F.is-equivariant-pos-map s g ⟩
        F.pos-map s ∘ (equivFun $ D.action (F.symm-map s g)) ∎

  ∣_∣₁ : ∀ {C D} → ActFaith [ C , D ] → Quot ℓ [ ∣ C ∣₀ , ∣ D ∣₀ ]
  ∣_∣₁ {C} {D} F = ∣F∣₁ where
    module F = Morphism F

    ∣F∣₁ : Quot ℓ [ _ , _ ]
    ∣F∣₁ .QMorphism.shape-mor = F.shape-map
    ∣F∣₁ .QMorphism.pos-equiv = pre-morphism-class $ ∣-∣₁-pre C D F

  ActFaith→QCont : Functor ActFaith (Quot ℓ)
  ActFaith→QCont .F-ob = ∣_∣₀
  ActFaith→QCont .F-hom = ∣_∣₁
  ActFaith→QCont .F-id {x = F} = QMorphism≡ $ isReflPremorphismEquiv $ ∣-∣₁-pre F F $ ActFaith.id {x = F}
  ActFaith→QCont .F-seq {x = F} {y = G} {z = H} f g = QMorphism≡ $ isReflPremorphismEquiv $ ∣-∣₁-pre F H $ ActFaith._⋆_ {x = F} {y = G} {z = H} f g
