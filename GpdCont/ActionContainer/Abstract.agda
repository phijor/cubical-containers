{-# OPTIONS --lossy-unification #-}
module GpdCont.ActionContainer.Abstract where

open import GpdCont.Prelude
open import GpdCont.Univalence using (uaCompEquivSquare)
open import GpdCont.HomotopySet using (_→Set_ ; ΠSet)
open import GpdCont.Group.SymmetricGroup
open import GpdCont.Group.DirProd using (module DirProd)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Pi using (ΠAction)
import GpdCont.GroupAction.Adjoint as AdjointAction

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (uncurry4 ; uncurry3)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using (Jequiv)
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties using (isPropIsGroup)
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom ; compGroupHom ; isPropIsGroupHom)
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)
open import Cubical.Algebra.Group.DirProd using (DirProd)


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
{-
[_⇒_] : ∀ {ℓ} (C D : ActionContainer ℓ) → ActionContainer ℓ
[ C ⇒ D ] = mkActionContainer S→T ΠQ⇒P ΠH×G Πσ⇒τ where
  open ActionContainer
  open module C = ActionContainer C using ()
    renaming
      ( Shape to S
      ; PosSet to P
      ; SymmGroup to G
      ; symmAction to σ
      )
  open module D = ActionContainer D using ()
    renaming
      ( Shape to T
      ; PosSet to Q
      ; SymmGroup to H
      ; symmAction to τ
      )

  S→T : hSet _
  S→T = C.ShapeSet →Set D.ShapeSet

  module _ (u : S → T) where
    H×G : (s : S) → Group _
    H×G s = DirProd (H (u s)) (G s)

    module H×G (s : S) = DirProd (H (u s)) (G s)

    Q⇒P : S → hSet _
    Q⇒P s = Q (u s) →Set P s

    ΠH×G : Group _
    ΠH×G = ΠGroup H×G

    ΠQ⇒P : hSet _
    ΠQ⇒P = ΠSet Q⇒P

    module σ⇒τ (s : S) = AdjointAction (H×G s) (Q (u s)) (P s)

    Πσ⇒τ : Action ΠH×G ΠQ⇒P
    Πσ⇒τ = ΠAction Q⇒P σ⇒τ where module _ (s : S) where
      τ* : Action (H×G s) (Q (u s))
      τ* = GroupHomPreCompAction (H×G.fstHom _) (τ (u s))

      σ* : Action (H×G s) (P s)
      σ* = GroupHomPreCompAction (H×G.sndHom _) (σ s)

      σ⇒τ = σ⇒τ.AdjointAction s τ* σ*

module ActionContainerMorphism {ℓ} (C D : ActionContainer ℓ) where
  private
    open module C = ActionContainer C using ()
      renaming
        ( Shape to S
        ; Pos to P
        ; Symm to G
        ; action to σ
        )
    open module D = ActionContainer D using ()
      renaming
        ( Shape to T
        ; Pos to Q
        ; Symm to H
        ; action to τ
        )

  isEquivariantPosMap : {u : S → T} (f : ∀ s → Q (u s) → P s) (φ : ∀ {s} → G s → H (u s)) → Type ℓ
  isEquivariantPosMap f φ = ∀ (s : S) (g : G s) → equivFun (σ g) ∘ f s ≡ f s ∘ equivFun (τ (φ g))

  isSymmGroupHom : {u : S → T} (φ : ∀ {s} → G s → H (u s)) → Type ℓ
  isSymmGroupHom {u} φ = ∀ (s : S) → IsGroupHom (C.symm-group-str s) (φ {s}) (D.symm-group-str (u s))

  record Morphismᴰ (shape-map : S → T) : Type ℓ where
    constructor mkMorphismᴰ
    field
      pos-map : ∀ s → Q (shape-map s) → P s
      symm-map : ∀ {s} → G s → H (shape-map s)

    field
      is-group-hom-symm-map : isSymmGroupHom symm-map
      is-equivariant-pos-map : isEquivariantPosMap pos-map symm-map

    symm-hom : ∀ s → GroupHom (C.SymmGroup s) (D.SymmGroup $ shape-map s)
    symm-hom s .fst = symm-map {s}
    symm-hom s .snd = is-group-hom-symm-map s

  record Morphism : Type ℓ where
    constructor _▷[_]
    field
      shape-map : S → T
      mor-str : Morphismᴰ shape-map

    open Morphismᴰ mor-str public

  open Morphismᴰ
  open Morphism

  mkMorphism : (u : S → T) (f : ∀ s → Q (u s) → P s) (φ : ∀ {s} → G s → H (u s))
    → isEquivariantPosMap f φ
    → isSymmGroupHom φ
    → Morphism
  mkMorphism u f φ is-equivariant-f is-group-hom-φ = λ where
    .shape-map → u
    .mor-str .pos-map → f
    .mor-str .symm-map → φ
    .mor-str .is-equivariant-pos-map → is-equivariant-f
    .mor-str .is-group-hom-symm-map → is-group-hom-φ

  mkMorphism-syntax : (u : S → T) (φ : ∀ s → GroupHom (C.SymmGroup s) (D.SymmGroup (u s))) (f : Σ[ f ∈ _ ] isEquivariantPosMap f (λ {s} → fst (φ s)))
    → Morphism
  mkMorphism-syntax u φ f = mkMorphism u (f .fst) (λ {s} → fst (φ s)) (f .snd) (snd ∘ φ)

  syntax mkMorphism-syntax u φ f = u ▷ f ◁ φ

  mkMorphismBundled : (u : S → T)
    → (φ : ∀ {s} → GroupHom (C.SymmGroup s) (D.SymmGroup (u s)))
    → Σ[ f ∈ (∀ s → Q (u s) → P s) ] isEquivariantPosMap f (φ .fst)
    → Morphism
  mkMorphismBundled = {! !}

module Transformation {ℓ} {C D : ActionContainer ℓ} where
  private
    open module C = ActionContainer C using ()
      renaming
        ( Shape to S
        ; Pos to P
        ; Symm to G
        ; action to σ
        )
    module G {s : S} = GroupStr (C.symm-group-str s)

    open module D = ActionContainer D using ()
      renaming
        ( Shape to T
        ; Pos to Q
        ; Symm to H
        ; isSetSymm to isSetH
        ; action to τ
        )
    module H {t : T} = GroupStr (D.symm-group-str t)

    open ActionContainerMorphism C D

  module _ (u : S → T) (F F′ : Morphismᴰ u) where
    open Morphismᴰ F using () renaming (pos-map to f ; symm-map to φ)
    open Morphismᴰ F′ using () renaming (pos-map to f′ ; symm-map to φ′)

    record Transformationᴰ : Type ℓ where
      field
        conjugator : (s : S) → H (u s)
        is-conjugate : ∀ {s} (g : G s) → (φ g) H.· (conjugator s) ≡ (conjugator s) H.· (φ′ g)
        is-pos-equiv : ∀ s → f s ≡ f′ s ∘ equivFun (τ (conjugator s))

  open Transformationᴰ

  module _ {u : S → T} {F F′ : Morphismᴰ u} where
    open Morphismᴰ F using () renaming (pos-map to f ; symm-map to φ)
    open Morphismᴰ F′ using () renaming (pos-map to f′ ; symm-map to φ′)

    TransformationᴰPath : ∀ {αᴰ βᴰ : Transformationᴰ u F F′} → αᴰ .conjugator ≡ βᴰ .conjugator → αᴰ ≡ βᴰ
    TransformationᴰPath p i .conjugator = p i
    TransformationᴰPath {αᴰ} {βᴰ} p i .is-conjugate {s} g = isProp→PathP {B = λ i → (φ g H.· p i s) ≡ (p i s H.· φ′ g)} (λ i → isSetH _ _ _) (αᴰ .is-conjugate g) (βᴰ .is-conjugate g) i
    TransformationᴰPath {αᴰ} {βᴰ} p i .is-pos-equiv s = isProp→PathP {B = λ i → f s ≡ f′ s ∘ equivFun (τ (p i s))}
      (λ i → isOfHLevelPath' 1 (isSet→ (C.is-set-pos _)) _ _)
      (αᴰ .is-pos-equiv s)
      (βᴰ .is-pos-equiv s)
      i

  idTransformationᴰ : {u : S → T} (F : Morphismᴰ u) → Transformationᴰ u F F
  idTransformationᴰ {u} F = def where
    open Morphismᴰ F using () renaming (pos-map to f ; symm-map to φ)
    def : Transformationᴰ u F F
    def .conjugator s = H.1g {u s}
    def .is-conjugate g =
      φ g H.· H.1g ≡⟨ H.·IdR _ ⟩
      φ g ≡⟨ sym $ H.·IdL _ ⟩
      H.1g H.· φ g ∎
    def .is-pos-equiv s =
      f s ≡⟨⟩
      f s ∘ equivFun (idEquiv _) ≡⟨ sym $ cong (λ h → f s ∘ equivFun h) (D.action-pres-1 {u s}) ⟩
      f s ∘ equivFun (τ H.1g) ∎

  vcompTransformationᴰ : {u : S → T} {F₀ F₁ F₂ : Morphismᴰ u}
    → Transformationᴰ u F₀ F₁
    → Transformationᴰ u F₁ F₂
    → Transformationᴰ u F₀ F₂
  vcompTransformationᴰ {u} {F₀} {F₁} {F₂} α β = def where
    module F₀ = Morphismᴰ F₀
    module F₁ = Morphismᴰ F₁
    module F₂ = Morphismᴰ F₂
    module α = Transformationᴰ α
    module β = Transformationᴰ β

    def : Transformationᴰ u _ _
    def .conjugator s = α.conjugator s H.· β.conjugator s
    def .is-conjugate = {! !}
    def .is-pos-equiv = {! !}
    
  data Transformation : (F F′ : Morphism) → Type ℓ where
    refl-shape :
      ∀ (u : S → T)
      → (F F′ : Morphismᴰ u)
      → (α : Transformationᴰ u F F′)
      → Transformation (u ▷[ F ]) (u ▷[ F′ ])

  module _ (F F′ : Morphism) where
    private
      open module F = Morphism F using () renaming (shape-map to u ; pos-map to f ; symm-map to φ)
      open module F′ = Morphism F′ using () renaming (shape-map to u′ ; pos-map to f′ ; symm-map to φ′)

    record TransformationP : Type ℓ where
      constructor mkTransformationP
      field
        shape-path : u ≡ u′
        {conjugator₀} : (s : S) → H (u s)
        {conjugator₁} : (s : S) → H (u′ s)
        conjugator-path : PathP (λ i → ∀ s → H (shape-path i s)) conjugator₀ conjugator₁
        is-conjugate : ∀ {s} (g : G s) → PathP (λ i → D.Symm (shape-path i s)) (φ g D.· conjugator₀ s) (conjugator₁ s D.· φ′ g)
        is-pos-equiv : ∀ s → PathP (λ i → ua (τ (conjugator-path i s)) i → P s) (f s) (f′ s)

    open TransformationP

    opaque
      TransformationPPath : {α β : TransformationP}
        → (conjugator₀-path : α .conjugator₀ ≡ β .conjugator₀)
        → (conjugator₁-path : α .conjugator₁ ≡ β .conjugator₁)
        → α ≡ β
      TransformationPPath {α} {β} conjugator₀-path conjugator₁-path = path where
        shape-square : α .shape-path ≡ β .shape-path
        shape-square = (isSet→ D.is-set-shape) u u′ (α .shape-path) (β .shape-path)

        conjugator-square : SquareP (λ i j → ∀ s → H (shape-square i j s)) (α .conjugator-path) (β .conjugator-path) conjugator₀-path conjugator₁-path
        conjugator-square = isSet→SquareP (λ i j → isSetΠ λ s → isSetH (shape-square i j s)) _ _ _ _

        is-conjugate-square : ∀ {s} (g : G s) → SquareP (λ i j → H (shape-square i j s))
          (α .is-conjugate g)
          (β .is-conjugate g)
          (λ i → φ g D.· (conjugator₀-path i s))
          (λ i → conjugator₁-path i s D.· (φ′ g))
        is-conjugate-square {s} g = isSet→SquareP (λ i j → isSetH (shape-square i j s)) _ _ _ _

        is-pos-equiv-square : ∀ s → SquareP (λ i j → ua (τ (conjugator-square i j s)) j → P s)
          (α .is-pos-equiv s)
          (β .is-pos-equiv s)
          (refl {x = f s})
          (refl {x = f′ s})
        is-pos-equiv-square s = isSet→SquareP (λ i j → isSet→ (C.is-set-pos s)) _ _ _ _

        path : α ≡ β
        path i .shape-path = shape-square i
        path i .conjugator₀ = conjugator₀-path i
        path i .conjugator₁ = conjugator₁-path i
        path i .conjugator-path = conjugator-square i
        path i .is-conjugate g j = is-conjugate-square g i j
        path i .is-pos-equiv s j = is-pos-equiv-square s i j

    TransformationPPath₀ : {α β : TransformationP}
      → (conjugator₀-path : α .conjugator₀ ≡ β .conjugator₀)
      → α ≡ β
    TransformationPPath₀ {α} {β} conjugator₀-path = TransformationPPath conjugator₀-path conjugator₁-path where
      shape-square : α .shape-path ≡ β .shape-path
      shape-square = (isSet→ D.is-set-shape) u u′ (α .shape-path) (β .shape-path)

      conjugator₁-path : α .conjugator₁ ≡ β .conjugator₁
      conjugator₁-path = doubleCompPathP (λ i j → ∀ s → H (shape-square j i s))
        (α .conjugator-path)
        conjugator₀-path
        (β .conjugator-path)

  module TransformationPElim (F : Morphism) where
    open module F = Morphism F using () renaming (mor-str to Fᴰ ; shape-map to u ; pos-map to f ; symm-map to φ)

    Motive : ∀ u′ → (u-path : u ≡ u′) → Type _
    Motive u′ shape-path =
      ∀ (F′ᴰ : Morphismᴰ u′)
      (open Morphismᴰ F′ᴰ using () renaming (pos-map to f′ ; symm-map to φ′))
      (let F′ = u′ ▷[ F′ᴰ ])
      --
      → (conjugator₀ : (s : S) → H (u s))
      → (conjugator₁ : (s : S) → H (u′ s))
      → (conjugator-path : PathP (λ i → ∀ s → H (shape-path i s)) conjugator₀ conjugator₁)
      → (is-conjugate : ∀ {s} (g : G s) → PathP (λ i → D.Symm (shape-path i s)) (φ g D.· conjugator₀ s) (conjugator₁ s D.· φ′ g))
      → (is-pos-equiv : ∀ s → PathP (λ i → ua (τ (conjugator-path i s)) i → P s) (f s) (f′ s))
      → Transformation F F′

    motive-reflᴰ : ∀ {F′ᴰ} {h₀} {h₁}
      (open Morphismᴰ F′ᴰ using () renaming (pos-map to f′ ; symm-map to φ′))
      → (h-path : h₀ ≡ h₁)
      → (h-conj : ∀ {s} (g : G s) → φ g D.· h₀ s ≡ h₁ s D.· φ′ g)
      → (h-pos-equiv : ∀ s → PathP (λ i → ua (τ (h-path i s)) i → P s) (f s) (f′ s))
      → Transformationᴰ u Fᴰ F′ᴰ
    motive-reflᴰ {h₀} h-path h-conj h-pos-equiv = λ where
      .Transformationᴰ.conjugator → h₀
      .Transformationᴰ.is-conjugate {s} g → h-conj {s} g ∙ cong (λ h → h s D.· _) (sym h-path)
      .Transformationᴰ.is-pos-equiv s i p → ua→⁻ (h-pos-equiv s) p i

    motive-refl : Motive u refl
    motive-refl F′ᴰ h₀ h₁ h-path h-conj h-pos-equiv = refl-shape u Fᴰ F′ᴰ $ motive-reflᴰ h-path h-conj h-pos-equiv

    elim : ∀ {u′} (p : u ≡ u′) → Motive u′ p
    elim = J Motive motive-refl

    elim-refl : elim refl ≡ motive-refl
    elim-refl = JRefl Motive motive-refl

    elim-refl-ext : ∀ {F′ᴰ} {conjugator} (is-conjugate : ∀ {s} (g : G s) → _) (is-pos-equiv : ∀ s → _)
      → elim refl F′ᴰ conjugator conjugator refl is-conjugate is-pos-equiv ≡ refl-shape u Fᴰ F′ᴰ (motive-reflᴰ refl is-conjugate is-pos-equiv)
    elim-refl-ext {F′ᴰ} {conjugator} is-conjugate is-pos-equiv i = elim-refl i F′ᴰ conjugator conjugator refl is-conjugate is-pos-equiv

  TransformationP→Transformation : {F F′ : Morphism} → TransformationP F F′ → Transformation F F′
  TransformationP→Transformation {F} {F′} = goal where
    open TransformationPElim F using (elim)

    goal : TransformationP F F′ → Transformation F F′
    goal (mkTransformationP shape-path conjugator-path is-conjugate is-pos-equiv)
      = elim shape-path (Morphism.mor-str F′) _ _ conjugator-path is-conjugate is-pos-equiv

  Transformation→TransformationP : {F F′ : Morphism} → Transformation F F′ → TransformationP F F′
  Transformation→TransformationP (refl-shape u F F′ α) = αP where
    αP : TransformationP _ _
    αP .TransformationP.shape-path = refl {x = u}
    αP .TransformationP.conjugator₀ = α .conjugator
    αP .TransformationP.conjugator₁ = α .conjugator
    αP .TransformationP.conjugator-path = refl {x = α .conjugator}
    αP .TransformationP.is-conjugate = α .is-conjugate
    αP .TransformationP.is-pos-equiv s = ua→ (funExt⁻ $ α .is-pos-equiv s)

  TransformationP-Transformation-Iso : ∀ {F F′ : Morphism} → Iso (TransformationP F F′) (Transformation F F′)
  TransformationP-Transformation-Iso .Iso.fun = TransformationP→Transformation
  TransformationP-Transformation-Iso .Iso.inv = Transformation→TransformationP
  TransformationP-Transformation-Iso {F = .(u ▷[ F ])} {F′ = .(u ▷[ F′ ])} .Iso.rightInv (refl-shape u F F′ α) =
    elim-refl-ext (α .is-conjugate) (λ s → ua→ $ funExt⁻ $ α .is-pos-equiv s) ∙ cong (refl-shape u F F′) (TransformationᴰPath refl)
    where
      open TransformationPElim (u ▷[ F ]) using (elim-refl ; elim-refl-ext)
  TransformationP-Transformation-Iso .Iso.leftInv αᴾ = {! !}
    -- TransformationPPath _ _ {! !} {! !}
    --
    -}
