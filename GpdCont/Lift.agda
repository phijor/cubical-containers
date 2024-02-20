module GpdCont.Lift where

open import GpdCont.Prelude hiding (Lift)

open import GpdCont.QuotientContainer as QC using (QCont)
open import GpdCont.GroupoidContainer as GC using (GCont)
open import GpdCont.Univalence as UA using (ua→ ; pathToEquiv ; ua)

open import Cubical.Data.Sigma.Base
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (isProp→SquareP ; flipSquare)
open import Cubical.HITs.GroupoidQuotients as GQ using (_//_)
open import Cubical.Functions.Embedding

module Lift {ℓ} (Q : QCont ℓ) where
  open QCont Q using (Shape ; Pos ; Symm ; _∼_ ; isTransSymm ; PosSet)

  opaque
    ↑Shape : Type ℓ
    ↑Shape = _//_ Shape {R = _∼_} isTransSymm

    ↑[_] : Shape → ↑Shape
    ↑[_] = GQ.[_]

    ↑// : ∀ {s t} → (r : s ∼ t) → ↑[ s ] ≡ ↑[ t ]
    ↑// = GQ.eq//


    ↑comp// : ∀ {s t u} (σ : s ∼ t) (τ : t ∼ u) → PathP (λ j → ↑[ s ] ≡ ↑// τ j) (↑// σ) (↑// (isTransSymm _ _ _ σ τ))
    ↑comp// = GQ.comp// {Rt = isTransSymm}

    isGroupoid-↑Shape : isGroupoid ↑Shape
    isGroupoid-↑Shape = GQ.squash//

    ↑Shape-elim : ∀ {ℓB} {B : ↑Shape → Type ℓB}
      → ((x : ↑Shape) → isGroupoid (B x))
      → (f : (s : Shape) → B ↑[ s ])
      → (feq : {a b : Shape} (r : a ∼ b) → PathP (λ i → B (↑// r i)) (f a) (f b))
      → ({a b c : Shape} (r : a ∼ b) (s : b ∼ c)
        → SquareP
          (λ i j → B (↑comp// r s i j))
          (feq r)
          (feq (isTransSymm a b c r s)) (refl {x = f a})
          (feq s))
      → (x : ↑Shape)
      → B x
    ↑Shape-elim = GQ.elim {A = Shape} {R = _∼_} isTransSymm

    ↑Shape-elimSet : ∀ {ℓB} {B : ↑Shape → Type ℓB}
      → ((x : ↑Shape) → isSet (B x))
      → (f : (s : Shape) → B ↑[ s ])
      → (feq : {s t : Shape} (σ : s ∼ t) → PathP (λ i → B (↑// σ i)) (f s) (f t))
      → (x : ↑Shape)
      → B x
    ↑Shape-elimSet = GQ.elimSet {A = Shape} {R = _∼_} isTransSymm

    ↑Shape-elimSet′ : ∀ {ℓB} {B : ↑Shape → Type ℓB}
      → (isInjectivePos : ∀ {s t} → Pos s ≃ Pos t → s ≡ t)
      → ((x : ↑Shape) → isSet (B x))
      → (f : (s : Shape) → B ↑[ s ])
      → (feq′ : {s : Shape} (σ : s ∼ s) → PathP (λ i → B (↑// σ i)) (f s) (f s))
      → (x : ↑Shape)
      → B x
    ↑Shape-elimSet′ {ℓB} {B} is-inj-pos is-set-shape f feq′ = ↑Shape-elimSet is-set-shape f feq where
      feq : {s t : Shape} (σ : s ∼ t) → PathP (λ i → B (↑// σ i)) (f s) (f t)
      feq {s} {t} = uncurry (λ σ → {! J Motive {! !} (is-inj-pos σ) !}) where
        Motive : (t : Shape) → s ≡ t → Type (ℓ-max ℓ ℓB)
        Motive t p = ∀ (is-sym-σ : Symm σ) → PathP (λ i → B (↑// (σ , is-sym-σ) i)) (f s) (f t)
          where
            σ : Pos s ≃ Pos t
            σ = pathToEquiv $ cong Pos p

    ↑Shape-rec : ∀ {ℓB} {B : Type ℓB}
       → isGroupoid B
       → (f : Shape → B) (feq : {a b : Shape} → a ∼ b → f a ≡ f b)
       → ({a b c : Shape} (r : a ∼ b) (s : b ∼ c)
        → Square (feq r) (feq (isTransSymm a b c r s)) refl (feq s))
      → ↑Shape → B
    ↑Shape-rec = GQ.rec {A = Shape} {R = _∼_} isTransSymm

  opaque
    unfolding ↑Shape PosSet
    ↑Pos′ : ↑Shape → hSet ℓ
    ↑Pos′ = GQ.rec isTransSymm isGroupoidHSet [_]* eq//* {! comp//* !} where
      [_]* : Shape → hSet ℓ
      [_]* = PosSet

      eq//* : ∀ {s t} → s ∼ t → [ s ]* ≡ [ t ]*
      eq//* (σ , _) = TypeOfHLevel≡ 2 $ ua σ

      -- TODO: This should follow:
      -- 1. This is a square of Σ′s with propositional second component
      -- 2. The first component is proofs _∼_ (a subtype of equivalences), they are closed under composition:
      --  2.1. Equivalences are closed under composition
      --  2.2. The relation is assumed to be an propositional equivalence relation
      comp//* : ∀ {s t u : Shape} → (s∼t : s ∼ t) (t∼u : t ∼ u) → Square (eq//* s∼t) (eq//* (isTransSymm s t u s∼t t∼u)) refl (eq//* t∼u)
      comp//* s∼t t∼u = ΣSquareSet (λ X → isProp→isSet isPropIsSet) {! !}

    ↑Pos : ↑Shape → Type ℓ
    ↑Pos = ⟨_⟩ ∘ ↑Pos′

    isSet-↑Pos : ∀ s → isSet (↑Pos s)
    isSet-↑Pos = str ∘ ↑Pos′

  ↑_ : GCont ℓ
  ↑ .GCont.Shape = ↑Shape
  ↑ .GCont.Pos = ↑Pos
  ↑ .GCont.is-groupoid-shape = isGroupoid-↑Shape
  ↑ .GCont.is-set-pos = isSet-↑Pos

module LiftΣ {ℓ} (Q : QCont ℓ) where
  open QCont Q using (Shape ; Pos ; Symm ; _∼_)

  module Q = QCont Q

  open import GpdCont.Delooping using (module Delooping)
  open import Cubical.HITs.SetQuotients as SQ using (_/_)

  record ↑Shape : Type ℓ where
    field
      ↓shape : Shape

    _·_ : (g h : ↓shape ∼ ↓shape) → ↓shape ∼ ↓shape
    _·_ = Q.isTransSymm _ _ _

    𝔹Pos = Delooping.𝔹 (↓shape ∼ ↓shape) _·_

    field
      symm : 𝔹Pos

  open ↑Shape

  ↑shape : (s : Shape) → ↑Shape
  ↑shape s .↓shape = s
  ↑shape s .symm = Delooping.⋆
  
  unquoteDecl ↑ShapeIsoΣ = declareRecordIsoΣ ↑ShapeIsoΣ (quote ↑Shape)

  instance
    ↑ShapeToΣ : RecordToΣ ↑Shape
    ↑ShapeToΣ = toΣ ↑ShapeIsoΣ

  isGroupoid-↑Shape : isGroupoid ↑Shape
  isGroupoid-↑Shape = recordIsOfHLevel 3 (isGroupoidΣ (isSet→isGroupoid Q.is-set-shape) λ ↓s → Delooping.isGroupoid𝔹)

  ↑ShapeLoop : ∀ {s : Shape} → s ∼ s → ↑shape s ≡ ↑shape s
  ↑ShapeLoop r i .↓shape = _
  ↑ShapeLoop r i .symm = Delooping.loop r i

  ↑Pos : ↑Shape → Type ℓ
  ↑Pos ↑s = (Pos $ ↑s .↓shape) -- × (↑s .symm ≡ ↑s .symm)

  isSet-↑Pos : ∀ s → isSet (↑Pos s)
  -- isSet-↑Pos ↑s = isSet× (Q.is-set-pos (↑s .↓shape)) (Delooping.isGroupoid𝔹 (↑s .symm) (↑s .symm))
  isSet-↑Pos ↑s = Q.is-set-pos (↑s .↓shape)

  ↑_ : GCont ℓ
  ↑ .GCont.Shape = ↑Shape
  ↑ .GCont.Pos = ↑Pos
  ↑ .GCont.is-groupoid-shape = isGroupoid-↑Shape
  ↑ .GCont.is-set-pos = isSet-↑Pos

module LiftLoop {ℓ} (Q : QCont ℓ) where
  open QCont Q using (Shape ; Pos ; Symm ; _∼_ ; isTransSymm ; PosSet)

  open import Cubical.Functions.Image

  private
    module Q = QCont Q

    _·_ : ∀ {s} → (g h : s ∼ s) → s ∼ s
    _·_ {s} = Q.isTransSymm s s s

  data ↑Shape : Type ℓ where
    ↑shape : Shape → ↑Shape
    ↑loop : ∀ {s} → s ∼ s → ↑shape s ≡ ↑shape s
    ↑loop-comp : ∀ {s} → (g h : s ∼ s) → PathP (λ j → ↑shape s ≡ ↑loop h j) (↑loop g) (↑loop (g · h))
    isGroupoid-↑Shape : isGroupoid ↑Shape

  ↑Shape-elim : ∀ {ℓB} {B : ↑Shape → Type ℓB}
    → (isOfHLevelDep 3 B)
    → (↑[_]* : (s : Shape) → B $ ↑shape s)
    → (↑loop* : {s : Shape} (g : s ∼ s) → PathP (λ i → B (↑loop g i)) ↑[ s ]* ↑[ s ]*)
    → (↑loop-comp* : {s : Shape} (g h : s ∼ s)
      → SquareP
        (λ i j → B (↑loop-comp g h i j))
        (↑loop* g)
        (↑loop* (g · h)) (refl {x = ↑[ s ]*})
        (↑loop* h))
    → (x : ↑Shape)
    → B x
  ↑Shape-elim {B} is-gpd-B ↑[_]* ↑loop* ↑loop-comp* = go where
    go : ∀ x → B x
    go (↑shape s) = ↑[ s ]*
    go (↑loop x i) = ↑loop* x i
    go (↑loop-comp g h j i) = ↑loop-comp* g h j i
    go (isGroupoid-↑Shape x y p q r s i j k) =
      is-gpd-B {x} {y}
        (go x) (go y)
        (cong go p) (cong go q)
        (cong (cong go) r) (cong (cong go) s)
        (isGroupoid-↑Shape x y p q r s)
        i j k

  ↑Shape-rec : ∀ {ℓB} {B : Type ℓB}
    → (isGroupoid B)
    → (↑[_]* : Shape → B)
    → (↑loop* : {s : Shape} (g : s ∼ s) → ↑[ s ]* ≡ ↑[ s ]*)
    → (↑loop-comp* : {s : Shape} (g h : s ∼ s)
      → Square
        (↑loop* g)
        (↑loop* (g · h)) (refl {x = ↑[ s ]*})
        (↑loop* h))
    → ↑Shape → B
  ↑Shape-rec {B} is-gpd-B = ↑Shape-elim {B = const B} λ x y p q r s _ → is-gpd-B x y p q r s

  ↑Shape-elimSetDep : ∀ {ℓB} {B : ↑Shape → Type ℓB}
    → (isOfHLevelDep 2 B)
    → (↑[_]* : (s : Shape) → B $ ↑shape s)
    → (↑loop* : {s : Shape} (g : s ∼ s) → PathP (λ i → B (↑loop g i)) ↑[ s ]* ↑[ s ]*)
    → (x : ↑Shape)
    → B x
  ↑Shape-elimSetDep {B} is-set-B ↑[_]* ↑loop* = ↑Shape-elim {B = B} is-gpd-B ↑[_]* ↑loop* ↑loop-comp* where
    is-gpd-B : isOfHLevelDep 3 B
    is-gpd-B b₀ b₁ = isPropDep→isSetDep (is-set-B b₀ b₁)

    opaque
      ↑loop-comp* : {s : Shape} (g h : s ∼ s)
        → SquareP
          (λ i j → B (↑loop-comp g h i j))
          (↑loop* g)
          (↑loop* (g · h)) (refl {x = ↑[ s ]*})
          (↑loop* h)
      ↑loop-comp* {s} g h = isSet→SquareP
        (λ i j x y p q → is-set-B x y p q λ _ _ → ↑loop-comp g h i j)
        (↑loop* g) (↑loop* (g · h)) refl (↑loop* h)

  ↑Shape-elimSet : ∀ {ℓB} {B : ↑Shape → Type ℓB}
    → (∀ x → isSet (B x))
    → (↑[_]* : (s : Shape) → B $ ↑shape s)
    → (↑loop* : {s : Shape} (g : s ∼ s) → PathP (λ i → B (↑loop g i)) ↑[ s ]* ↑[ s ]*)
    → (x : ↑Shape)
    → B x
  ↑Shape-elimSet is-set-B = ↑Shape-elimSetDep λ {a0} {a1} → isOfHLevel→isOfHLevelDep 2 is-set-B {a0} {a1}

  ↑Shape-elimPropDep : ∀ {ℓB} {B : ↑Shape → Type ℓB}
    → (isPropDep B)
    → (↑[_]* : (s : Shape) → B $ ↑shape s)
    → (x : ↑Shape)
    → B x
  ↑Shape-elimPropDep {B} is-prop-B ↑[_]* = ↑Shape-elim {B = B} is-gpd-B ↑[_]* ↑loop* ↑loop-comp* where
    is-gpd-B : isOfHLevelDep 3 B
    is-gpd-B {a0} {a1} = isOfHLevelDepSuc 2
      (λ {a0} {a1} → isOfHLevelDepSuc 1 (λ {a0} {a1} → is-prop-B) {a0} {a1}) {a0} {a1}

    opaque
      ↑loop* : {s : Shape} (g : s ∼ s) → PathP (λ i → B (↑loop g i)) ↑[ s ]* ↑[ s ]*
      ↑loop* {s} g = is-prop-B ↑[ s ]* ↑[ s ]* (↑loop g)

      ↑loop-comp* : {s : Shape} (g h : s ∼ s)
        → SquareP
          (λ i j → B (↑loop-comp g h i j))
          (↑loop* g)
          (↑loop* (g · h)) (refl {x = ↑[ s ]*})
          (↑loop* h)
      ↑loop-comp* {s} g h = isProp→SquareP
        (λ i j x y → is-prop-B x y λ _ → ↑loop-comp g h i j)
        refl (↑loop* h) (↑loop* g) (↑loop* (g · h))

  ↑Shape-elimProp : ∀ {ℓB} {B : ↑Shape → Type ℓB}
    → (∀ x → isProp (B x))
    → (↑[_]* : (s : Shape) → B $ ↑shape s)
    → (x : ↑Shape)
    → B x
  ↑Shape-elimProp {B} is-prop-B = ↑Shape-elimPropDep {B = B} λ {a0} {a1} → isOfHLevel→isOfHLevelDep 1 is-prop-B {a0} {a1}

  opaque
    unfolding PosSet isTransSymm
    ↑Pos′ : ↑Shape → hSet ℓ
    ↑Pos′ = ↑Shape-rec isGroupoidHSet PosSet ↑loop* ↑loop-comp* where
      ↑loop* : ∀ {s} → s ∼ s → PosSet s ≡ PosSet s
      ↑loop* = TypeOfHLevel≡ 2 ∘ ua ∘ fst

      ↑loop-comp*′ : ∀ {s} (σ τ : Pos s ≃ Pos s) → Square (ua σ) (ua (σ ∙ₑ τ)) refl (ua τ)
      ↑loop-comp*′ = UA.uaCompEquivSquare

      ↑loop-comp* : ∀ {s} (g h : s ∼ s) → Square (↑loop* g) (↑loop* (g · h)) refl (↑loop* h)
      ↑loop-comp* g h = ΣSquareSet (λ X → isProp→isSet isPropIsSet) (↑loop-comp*′ (g .fst) (h .fst))

    ↑Pos : ↑Shape → Type ℓ
    ↑Pos = ⟨_⟩ ∘ ↑Pos′

    isSet-↑Pos : ∀ s → isSet (↑Pos s)
    isSet-↑Pos = str ∘ ↑Pos′

  ↑_ : GCont ℓ
  ↑ .GCont.Shape = ↑Shape
  ↑ .GCont.Pos = ↑Pos
  ↑ .GCont.is-groupoid-shape = isGroupoid-↑Shape
  ↑ .GCont.is-set-pos = isSet-↑Pos

module Properties {ℓ} (Q : QCont ℓ)  where
  open import Cubical.Data.Sigma.Properties
  open import Cubical.Foundations.Isomorphism using (Iso ; section ; retract ; isoToEquiv)
  open module Q = QCont Q using (Shape ; Pos ; Symm ; _∼_ ; isTransSymm ; PosSet)
  open LiftLoop Q

  module Delooping (s : Shape) where
    open import GpdCont.Delooping using (module Delooping)
    open Delooping (s ∼ s) _·_ public

  open Delooping public

  Σ𝔹 : Type ℓ
  Σ𝔹 = Σ[ s ∈ Shape ] Delooping.𝔹 s

  isGroupoid-Σ𝔹 : isGroupoid Σ𝔹
  isGroupoid-Σ𝔹 = isGroupoidΣ (isSet→isGroupoid Q.is-set-shape) λ s → isGroupoid𝔹

  module ↑Shape-Delooping-Iso where
    fun : ↑Shape → Σ𝔹
    fun = ↑Shape-rec isGroupoid-Σ𝔹 [_]* [-]*-loop [-]*-comp where
      [_]* : Shape → Σ𝔹
      [ s ]* .fst = s
      [ s ]* .snd = ⋆

      [-]*-loop : ∀ {s} → s ∼ s → [ s ]* ≡ [ s ]*
      [-]*-loop {s} σ = ΣPathP (refl {x = s}, loop σ)

      [-]*-comp : ∀ {s} (g h : s ∼ s) → Square ([-]*-loop g) ([-]*-loop (g · h)) refl ([-]*-loop h)
      [-]*-comp {s} g h i j .fst = s
      [-]*-comp {s} g h i j .snd = loop-comp g h i j

    inv : Σ𝔹 → ↑Shape
    inv = uncurry λ s → Delooping.rec s isGroupoid-↑Shape (↑shape s) ↑loop ↑loop-comp

    rightInv : section fun inv
    rightInv = uncurry goal where module _ (s : Shape) where
      is-gpd-path : ∀ s (g : Delooping.𝔹 s) → isGroupoid (fun (inv (s , g)) ≡ (s , g))
      is-gpd-path s g = isSet→isGroupoid (isGroupoid-Σ𝔹 _ (s , g))

      -- [fun] and [inv] compute on constructors of `𝔹 s`
      goal : ∀ (g : Delooping.𝔹 s) → fun (inv (s , g)) ≡ (s , g)
      goal = Delooping.elim s (is-gpd-path s)
        refl
        (λ σ i → refl {x = s , loop σ i})
        (λ σ τ i j → refl {x = s , Delooping.loop-comp σ τ i j})

    -- TODO: Use [↑Shape-elim] and prove coherence of composition explicitly.
    leftInv : retract fun inv
    leftInv = ↑Shape-elimSet (λ ↑s → isGroupoid-↑Shape _ ↑s) (λ s → refl {x = ↑shape s}) λ { g → flipSquare (refl {x = ↑loop g}) }

  ↑Shape-Delooping-Iso : Iso ↑Shape Σ𝔹
  ↑Shape-Delooping-Iso = record { ↑Shape-Delooping-Iso }

  open ↑Shape-Delooping-Iso using () renaming (fun to ↑Shape→Σ𝔹 ; inv to Σ𝔹→↑Shape) public

  ↑Shape-Delooping-equiv : ↑Shape ≃ Σ𝔹
  ↑Shape-Delooping-equiv = isoToEquiv ↑Shape-Delooping-Iso

  opaque
    unfolding PosSet
    ΣPos : (↑s : Σ𝔹) → hSet _
    ΣPos = uncurry λ s → Delooping.rec s isGroupoidHSet (PosSet s) (λ σ → TypeOfHLevel≡ 2 (ua (σ .fst))) {! !}

--   opaque
--     unfolding ↑Pos
--     ↑Pos-Delooping-equiv : ∀ (↑s : ↑Shape) → ↑Pos ↑s ≃ (Pos (fst $ ↑Shape→Σ𝔹 ↑s))
--     ↑Pos-Delooping-equiv = ↑Shape-elimSet (λ ↑s → isOfHLevel≃ 2 (isSet-↑Pos ↑s) (Q.is-set-pos _)) ? {! !} where
--       -- eq-path : ∀ {s} (g : s ∼ s) → PathP (λ i → (ua (fst g) i) ≃ Pos s) (idEquiv _) (idEquiv _)
--       -- eq-path g i = UA.ua-unglue-equiv′ (g .fst) i
