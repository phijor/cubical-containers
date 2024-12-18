{-# OPTIONS --lossy-unification #-}
module GpdCont.ActionContainer.Base where

open import GpdCont.Prelude
open import GpdCont.Univalence using (ua ; uaCompEquiv ; uaCompEquivSquare)
open import GpdCont.Group.SymmetricGroup
open import GpdCont.GroupAction.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (uncurry4 ; uncurry3)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties using (isPropIsGroup)
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom ; compGroupHom ; isPropIsGroupHom)

record ActionContainer (ℓ : Level) : Type (ℓ-suc ℓ) where
  no-eta-equality
  field
    Shape : Type ℓ
    Pos : (s : Shape) → Type ℓ
    Symm : (s : Shape) → Type ℓ
    action : {s : Shape} → Symm s → (Pos s ≃ Pos s)

  field
    is-set-shape : isSet Shape
    is-set-pos : ∀ s → isSet (Pos s)

  PosSymGroup : (s : Shape) → Group ℓ
  PosSymGroup s = 𝔖 (Pos s , is-set-pos s)

  field
    symm-group-str : ∀ s → GroupStr (Symm s)
    is-group-hom-action : ∀ s → IsGroupHom (symm-group-str s) (action {s}) (str $ PosSymGroup s)

  ShapeSet : hSet ℓ
  ShapeSet .fst = Shape
  ShapeSet .snd = is-set-shape

  PosSet : (s : Shape) → hSet ℓ
  PosSet s .fst = Pos s
  PosSet s .snd = is-set-pos s

  SymmGroup : (s : Shape) → Group ℓ
  SymmGroup s .fst = Symm s
  SymmGroup s .snd = symm-group-str s

  isSetSymm : ∀ s → isSet (Symm s)
  isSetSymm s = symm-group-str s .GroupStr.is-set

  PosLoop : {s : Shape} → Symm s → PosSet s ≡ PosSet s
  PosLoop = TypeOfHLevel≡ 2 ∘ ua ∘ action

  _·_ : ∀ {s} → (g h : Symm s) → Symm s
  _·_ {s} = GroupStr._·_ (symm-group-str s)

  symm-id : ∀ {s} → Symm s
  symm-id {s} = GroupStr.1g (symm-group-str s)

  symm-inv : ∀ {s} → Symm s → Symm s
  symm-inv {s} = GroupStr.inv (symm-group-str s)

  opaque
    PosLoopCompSquare : {s : Shape} → (g h : Symm s) → compSquareFiller (PosLoop g) (PosLoop h) (PosLoop (g · h))
    PosLoopCompSquare g h = ΣSquareSet (λ X → isProp→isSet isPropIsSet) goal where
      goal : compSquareFiller (ua $ action g) (ua $ action h) (ua $ action (g · h))
      goal = coerceCompSquareFiller $
        (ua $ action g) ∙ (ua $ action h) ≡⟨ sym $ uaCompEquiv (action g) (action h) ⟩
        (ua $ action g ∙ₑ action h) ≡⟨ sym $ cong ua (IsGroupHom.pres· (is-group-hom-action _) g h) ⟩
        (ua $ action (g · h)) ∎

  actionHom : ∀ s → GroupHom (SymmGroup s) (PosSymGroup s)
  actionHom s .fst = action {s}
  actionHom s .snd = is-group-hom-action s

  symmAction : (s : Shape) → Action (SymmGroup s) (PosSet s)
  symmAction s = GroupHom→Action (actionHom s)

  action-pres-1 : ∀ {s} → action (GroupStr.1g (symm-group-str s)) ≡ idEquiv (Pos s)
  action-pres-1 = IsGroupHom.pres1 (is-group-hom-action _)

  action-pres-inv : ∀ {s} (g : Symm s) → action (symm-inv g) ≡ invEquiv (action g)
  action-pres-inv = IsGroupHom.presinv (is-group-hom-action _)

  action-pres-· : ∀ {s} (g h : Symm s) → action (g · h) ≡ action g ∙ₑ action h
  action-pres-· = IsGroupHom.pres· (is-group-hom-action _)

open ActionContainer

ActionContainer≡ : ∀ {ℓ} {C D : ActionContainer ℓ}
  → (shape : C .Shape ≡ D .Shape)
  → (pos : PathP (λ i → shape i → Type ℓ) (C .Pos) (D .Pos))
  → (symm : PathP (λ i → shape i → Group ℓ) (SymmGroup C) (SymmGroup D))
  → (action : PathP (λ i → ∀ {s : shape i} → ⟨ symm i s ⟩ → (pos i s ≃ pos i s)) (C .action) (D .action))
  → C ≡ D
ActionContainer≡ {C} {D} shape pos symm action′ = go where

  opaque
    go-is-set-shape : PathP (λ i → isSet (shape i)) (C .is-set-shape) (D .is-set-shape)
    go-is-set-shape = isProp→PathP (λ i → isPropIsSet {A = shape i}) _ _

    go-is-set-pos : PathP (λ i → ∀ s → isSet (pos i s)) (C .is-set-pos) (D .is-set-pos)
    go-is-set-pos = isProp→PathP (λ i → isPropΠ λ s → isPropIsSet {A = pos i s}) _ _

    go-is-group-hom-action : PathP (λ i → ∀ s → IsGroupHom (symm i s .snd) (action′ i {s}) (str (𝔖 (pos i s , go-is-set-pos i s)))) (C .is-group-hom-action) (D .is-group-hom-action)
    go-is-group-hom-action = isProp→PathP (λ i → isPropΠ λ _ → isPropIsGroupHom _ _) _ _

  go : C ≡ D
  go i .Shape = shape i
  go i .Pos = pos i
  go i .Symm = fst ∘ symm i
  go i .action = action′ i
  go i .is-set-shape = go-is-set-shape i
  go i .is-set-pos = go-is-set-pos i
  go i .symm-group-str = snd ∘ symm i
  go i .is-group-hom-action = go-is-group-hom-action i

mkActionContainer : ∀ {ℓ} (S : hSet ℓ) (P : ⟨ S ⟩ → hSet ℓ) (G : ⟨ S ⟩ → Group ℓ) (σ : ∀ s → Action (G s) (P s)) → ActionContainer ℓ
mkActionContainer S P G σ .ActionContainer.Shape = ⟨ S ⟩
mkActionContainer S P G σ .ActionContainer.Pos = ⟨_⟩ ∘ P
mkActionContainer S P G σ .ActionContainer.Symm = ⟨_⟩ ∘ G
mkActionContainer S P G σ .ActionContainer.action {s} = σ s .Action.action
mkActionContainer S P G σ .ActionContainer.is-set-shape = str S
mkActionContainer S P G σ .ActionContainer.is-set-pos = str ∘ P
mkActionContainer S P G σ .ActionContainer.symm-group-str = str ∘ G
mkActionContainer S P G σ .ActionContainer.is-group-hom-action s = Action→GroupHom (σ s) .snd

unbundleContainer : ∀ {ℓ} (C : ActionContainer ℓ)
  → Σ[ S ∈ hSet ℓ ]
    Σ[ P ∈ (⟨ S ⟩ → hSet ℓ) ]
    Σ[ G ∈ (⟨ S ⟩ → Group ℓ) ]
    ∀ s → Action (G s) (P s)
unbundleContainer C = let module C = ActionContainer C in
  λ where
    .fst → C.ShapeSet
    .snd .fst → C.PosSet
    .snd .snd .fst → C.SymmGroup
    .snd .snd .snd → C.symmAction
{-# INLINE unbundleContainer #-}

ActionContainerIsoΣ : ∀ {ℓ} → Iso (ActionContainer ℓ) (Σ[ S ∈ hSet ℓ ] Σ[ P ∈ (⟨ S ⟩ → hSet ℓ) ] Σ[ G ∈ (⟨ S ⟩ → Group ℓ) ] ((s : ⟨ S ⟩) → Action (G s) (P s)))
ActionContainerIsoΣ .Iso.fun = unbundleContainer
ActionContainerIsoΣ .Iso.inv = uncurry3 mkActionContainer
ActionContainerIsoΣ .Iso.rightInv _ = refl
ActionContainerIsoΣ .Iso.leftInv C = ActionContainer≡ refl refl symm-group-path refl where
  module Symm s = GroupStr (str (SymmGroup C s))
  symm-group-path : SymmGroup _ ≡ SymmGroup C
  symm-group-path i s .fst = Symm C s
  symm-group-path i s .snd .GroupStr.1g = Symm.1g s
  symm-group-path i s .snd .GroupStr._·_ = Symm._·_ s
  symm-group-path i s .snd .GroupStr.inv = Symm.inv s
  symm-group-path i s .snd .GroupStr.isGroup = Symm.isGroup s

ActionContainer≃Σ : ∀ {ℓ} → (ActionContainer ℓ) ≃ (Σ[ S ∈ hSet ℓ ] Σ[ P ∈ (⟨ S ⟩ → hSet ℓ) ] Σ[ G ∈ (⟨ S ⟩ → Group ℓ) ] ((s : ⟨ S ⟩) → Action (G s) (P s)))
ActionContainer≃Σ = isoToEquiv ActionContainerIsoΣ
