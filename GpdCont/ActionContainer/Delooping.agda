{-# OPTIONS --lossy-unification #-}
module GpdCont.ActionContainer.Delooping where

open import GpdCont.Prelude hiding (Lift)
open import GpdCont.Univalence using (ua→ua)

open import GpdCont.ActionContainer.Abstract
import GpdCont.ActionContainer.Morphism as ACMorphism
import GpdCont.ActionContainer.Transformation as ACTransformation

open import GpdCont.GroupoidContainer.Base renaming (GCont to SymmetricContainer)
open import GpdCont.GroupoidContainer.Morphism renaming (GContMorphism to SymmetricContainerMorphism ; GContMorphism≡Equiv to SymmetricContainerMorphism≡Equiv)

import GpdCont.Delooping as Delooping
import GpdCont.Delooping.Map as DeloopingMap

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path as Path using ()
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Morphisms

module Lift {ℓ} (C : ActionContainer ℓ) where
  private
    open module C = ActionContainer C using ()
      renaming
        ( Shape to S
        ; Pos to P
        ; PosSet to PSet
        ; Symm to G
        ; action to σ
        )

  module BG {s : S} = Delooping (G s) (C.symm-group-str s)

  Shape : Type ℓ
  Shape = Σ[ s ∈ S ] BG.𝔹 {s}

  is-groupoid-shape : isGroupoid Shape
  is-groupoid-shape = isGroupoidΣ (isSet→isGroupoid C.is-set-shape) λ s → BG.isGroupoid𝔹 {s}

  PosSet : Shape → hSet ℓ
  PosSet = uncurry goal where module _ (s : S) where
    P⋆ : hSet ℓ
    P⋆ = PSet s

    P-loop : G s → P⋆ ≡ P⋆
    P-loop = C.PosLoop

    goal : BG.𝔹 {s} → hSet ℓ
    goal = BG.rec isGroupoidHSet P⋆ P-loop $ C.PosLoopCompSquare {s}

  Pos : Shape → Type ℓ
  Pos = ⟨_⟩ ∘ PosSet

  is-set-pos : ∀ s → isSet (Pos s)
  is-set-pos = str ∘ PosSet
  
  Lift : SymmetricContainer ℓ
  Lift .SymmetricContainer.Shape = Shape
  Lift .SymmetricContainer.Pos = Pos
  Lift .SymmetricContainer.is-groupoid-shape = is-groupoid-shape
  Lift .SymmetricContainer.is-set-pos = is-set-pos

open Lift using (Lift)

module LiftMorphism {ℓ} {C D : ActionContainer ℓ} (F : ACMorphism.Morphism C D) where
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

  open Lift C using () renaming (module BG to BG)
  open Lift D using () renaming (module BG to BH)

  open ACMorphism.Morphism F using ()
    renaming
      ( shape-map to u
      ; pos-map to f
      ; is-equivariant-pos-map to is-equivariant-f
      ; symm-map to φ
      ; symm-hom to φ-hom
      )

  shape-mor : (Σ[ s ∈ S ] BG.𝔹 {s}) → (Σ[ t ∈ T ] BH.𝔹 {t})
  shape-mor (s , _) .fst = u s
  shape-mor (s , x) .snd = DeloopingMap.map (φ-hom s) x

  pos-mor : (s* : Lift.Shape C) → ⟨ Lift.PosSet D (shape-mor s*) ⟩ → ⟨ Lift.PosSet C s* ⟩
  pos-mor (s , x) = BG.elimSet {B = Motive} isSetMotive f⋆ f⋆-loop x where
    Motive : (x : BG.𝔹 {s}) → Type _
    Motive x = ⟨ Lift.PosSet D (shape-mor (s , x)) ⟩ → ⟨ Lift.PosSet C (s , x) ⟩

    isSetMotive : ∀ x → isSet (Motive x)
    isSetMotive x = isSet→ $ str $ Lift.PosSet C _

    f⋆ : Q (u s) → P s
    f⋆ = f s

    f⋆-equivariant : (g : G s) (q : Q (u s)) → equivFun (σ g) (f s q) ≡ f s (equivFun (τ $ φ s g) q)
    f⋆-equivariant g q = funExt⁻ (is-equivariant-f s g) q

    f⋆-loop : (g : G s) → PathP (λ i → ua (τ (φ s g)) i → ua (σ g) i) f⋆ f⋆
    f⋆-loop g = ua→ua (f⋆-equivariant g)

  LiftMorphism : SymmetricContainerMorphism (Lift C) (Lift D)
  LiftMorphism .SymmetricContainerMorphism.shape-mor = shape-mor
  LiftMorphism .SymmetricContainerMorphism.pos-path = pos-mor

open LiftMorphism using (LiftMorphism)

module _ {ℓ} (C D : ActionContainer ℓ)where
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

    open module Lift-C = Lift C using () renaming (module BG to BG)
    open module Lift-D = Lift D using () renaming (module BG to BH)

    open ACMorphism C D using (mkMorphism ; Morphism ; Morphismᴰ ; _▷[_])
    open ACTransformation {C = C} {D = D} using (Transformationᴰ)

  module LiftMorphismPathJ
    (u : S → T)
    (F F′ : Morphismᴰ u)
    (α : Transformationᴰ u F F′)
    where
    -- (u : S → T)
    -- (f f′ : ∀ s → Q (u s) → P s)
    -- (φ φ′ : ∀ {s} → G s → H (u s))
    -- (is-group-hom-φ : ∀ s → IsGroupHom (C.symm-group-str s) (φ {s}) (D.symm-group-str (u s)))
    -- (is-group-hom-φ′ : ∀ s → IsGroupHom (C.symm-group-str s) (φ′ {s}) (D.symm-group-str (u s)))
    -- (is-equivariant-f : ∀ s g → equivFun (σ g) ∘ f s ≡ f s ∘ equivFun (τ (φ g)))
    -- (is-equivariant-f′ : ∀ s g → equivFun (σ g) ∘ f′ s ≡ f′ s ∘ equivFun (τ (φ′ g)))

    -- (h : ∀ s → H (u s))
    -- (h-adj : ∀ {s} (g : G s) → (φ g D.· h s) ≡ (h s D.· φ′ g))
    -- (f-comm : ∀ s → f s ≡ f′ s ∘ equivFun (τ (h s)))
    -- where
    private
      open module F = Morphismᴰ F using () renaming (pos-map to f ; symm-map to φ)
      open module F′ = Morphismᴰ F′ using () renaming (pos-map to f′ ; symm-map to φ′)
      module α = Transformationᴰ α

    module Lift-F = LiftMorphism (u ▷[ F ])
    module Lift-F′ = LiftMorphism (u ▷[ F′ ])

    shape-mor-path : Lift-F.shape-mor ≡ Lift-F′.shape-mor
    shape-mor-path = funExt λ (s , x)
      → ΣPathP (refl {x = u s} , DeloopingMap.map≡-ext (α.conjugator s) (α.is-conjugate s) x)

    pos-mor-path : ∀ s* →
      PathP (λ i → Lift-D.Pos (shape-mor-path i s*) → Lift-C.Pos s*) (Lift-F.pos-mor s*) (Lift-F′.pos-mor s*)
    pos-mor-path (s , x) = BG.elimProp {B = Motive s} (isPropMotive s) (pos-mor-path⋆ s) x where module _ (s : S) where
      Motive : (x : BG.𝔹 {s}) → Type _
      Motive x = PathP (λ i → Lift-D.Pos (shape-mor-path i (s , x)) → Lift-C.Pos (s , x)) (Lift-F.pos-mor (s , x)) (Lift-F′.pos-mor (s , x))

      isPropMotive : ∀ x → isProp (Motive x)
      isPropMotive x = isOfHLevelPathP' 1 (isSet→ (Lift-C.is-set-pos _)) _ _

      pos-mor-path⋆ : PathP (λ i → ua (τ (α.conjugator s)) i → P s) (f s) (f′ s)
      pos-mor-path⋆ = ua→ (funExt⁻ (α.is-pos-equiv s))

    LiftMorphismPath : LiftMorphism (u ▷[ F ]) ≡ LiftMorphism (u ▷[ F′ ])
    LiftMorphismPath i .SymmetricContainerMorphism.shape-mor = shape-mor-path i
    LiftMorphismPath i .SymmetricContainerMorphism.pos-path s* = pos-mor-path s* i

  module LiftMorphismPath (F G : Morphism) where
    open ACTransformation {C = C} {D = D} using (Transformation ; TransformationP)
    LiftMorphismPath : Transformation F G → LiftMorphism F ≡ LiftMorphism G
    LiftMorphismPath (Transformation.refl-shape u F F′ α) = LiftMorphismPathJ.LiftMorphismPath u F F′ α

    LiftMorphismPathP : TransformationP F G → LiftMorphism F ≡ LiftMorphism G
    LiftMorphismPathP α = goal where
      open module F = Morphism F using () renaming (pos-map to f ; symm-map to φ ; symm-hom to φ*)
      open module F′ = Morphism G using () renaming (pos-map to g ; symm-map to ψ ; symm-hom to ψ*)
      module α = TransformationP α

      shape-mor-path : (LiftMorphism.shape-mor F) ≡ (LiftMorphism.shape-mor G)
      shape-mor-path = funExt $ uncurry λ s x → ΣPathP (funExt⁻ α.shape-path s , foo s x) where
        foo : ∀ s (x : BG.𝔹 {s}) → PathP (λ i → BH.𝔹 {α.shape-path i s}) (DeloopingMap.map (φ* s) x) (DeloopingMap.map (ψ* s) x)
        foo s = BG.elimSet {B = λ x → PathP (λ i → BH.𝔹 {α.shape-path i s}) (DeloopingMap.map (φ* s) x) (DeloopingMap.map (ψ* s) x)}
          (λ x → {! !})
          (λ { i → BH.loop (α.conjugator-path i s) i })
          {! !}

      goal : LiftMorphism F ≡ LiftMorphism G
      goal i .SymmetricContainerMorphism.shape-mor = shape-mor-path i
      goal i .SymmetricContainerMorphism.pos-path = {! !}

  module UnliftMorphismPath (F F′ : Morphism) where
    open ACTransformation {C = C} {D = D} using (Transformation ; TransformationP)
    UnliftMorphismPath : LiftMorphism F ≡ LiftMorphism F′ → Transformation F F′
    UnliftMorphismPath p = {! !}

    open ACMorphism.Morphism F using ()
      renaming
        ( shape-map to u
        ; pos-map to f
        ; is-equivariant-pos-map to is-equivariant-f
        ; symm-map to φ
        ; symm-hom to φ-hom
        )
    open ACMorphism.Morphism F′ using ()
      renaming
        ( shape-map to u′
        ; pos-map to f′
        ; is-equivariant-pos-map to is-equivariant-f′
        ; symm-map to φ′
        ; symm-hom to φ′-hom
        )


    open TransformationP

    emb : (LiftMorphism F ≡ LiftMorphism F′) ≃ (TransformationP F F′)
    emb =
      (LiftMorphism F ≡ LiftMorphism F′) ≃⟨ invEquiv SymmetricContainerMorphism≡Equiv ⟩
      ( Σ[ p ∈ LiftMorphism.shape-mor F ≡ LiftMorphism.shape-mor F′ ]
        (∀ s → PathP (λ i → Lift.Pos D (p i s) → Lift.Pos C s) (LiftMorphism.pos-mor F s) (LiftMorphism.pos-mor F′ s))
      )
      ≃⟨ {! !} ⟩
      ( Σ[ pₛ ∈ u ≡ u′ ] Σ[ pₚ ∈ PathP (λ i → ∀ s → BG.𝔹 {s} → BH.𝔹 {pₛ i s}) (DeloopingMap.map ∘ φ-hom) (DeloopingMap.map ∘ φ′-hom) ]
        (∀ s → PathP (λ i → Lift.Pos D (pₛ i (s .fst) , pₚ i _ (s .snd)) → Lift.Pos C s) (LiftMorphism.pos-mor F s) (LiftMorphism.pos-mor F′ s))
      )
      ≃⟨ Σ-cong-equiv-snd
        -- (λ pₛ → {!funExtEquiv {A = S} {B = λ s i → BG.𝔹 {s} → BH.𝔹 {pₛ i s}} {f = DeloopingMap.map ∘ φ-hom} {g = DeloopingMap.map ∘ φ′-hom}!})
        (λ pₛ → {!funExt₂Equiv {A = S} {B = λ s → BG.𝔹 {s}} {C = λ s _ i → BH.𝔹 {pₛ i s}} {f = λ s x → DeloopingMap.map (φ-hom s) x} {g = λ s x → DeloopingMap.map (φ′-hom s) x}!})
      ⟩
      -- ( Σ[ pₛ ∈ u ≡ u′ ] Σ[ pₚ ∈ (∀ s → PathP (λ i → BG.𝔹 {s} → BH.𝔹 {pₛ i s}) (DeloopingMap.map (φ-hom s)) (DeloopingMap.map (φ′-hom s))) ]
      --   (∀ s → PathP (λ i → Lift.Pos D (pₛ i (s .fst) , pₚ (s .fst) i (s .snd)) → Lift.Pos C s) (LiftMorphism.pos-mor F s) (LiftMorphism.pos-mor F′ s))
      -- )
      -- ≃⟨ {! !} ⟩
      ( Σ[ pₛ ∈ u ≡ u′ ] Σ[ pₚ ∈ (∀ s (x : BG.𝔹 {s}) → PathP (λ i → BH.𝔹 {pₛ i s}) (DeloopingMap.map (φ-hom s) x) (DeloopingMap.map (φ′-hom s) x)) ]
        (∀ s → PathP (λ i → Lift.Pos D (pₛ i (s .fst) , pₚ (s .fst) (s .snd) i) → Lift.Pos C s) (LiftMorphism.pos-mor F s) (LiftMorphism.pos-mor F′ s))
      )
      ≃⟨ {! !} ⟩
      ( Σ[ p ∈ (u ≡ u′) ]
        Σ[ h₀ ∈ (∀ s → H (u s)) ]
        Σ[ h₁ ∈ (∀ s → H (u′ s)) ]
        Σ[ conj-h ∈ (PathP (λ i → ∀ s → H (p i s)) h₀ h₁) ]
        (∀ s (g : G s) → PathP (λ i → H (p i s)) (φ s g D.· h₀ s) (h₁ s D.· φ′ s g))
          ×
        (∀ s → PathP (λ i → ua (τ (conj-h i s)) i → P s) (f s) (f′ s))
      )
        ≃⟨ Σ≃ (TransformationP F F′) ⟩
      (TransformationP F F′) ≃∎


    UnliftMorphismPathP : LiftMorphism F ≡ LiftMorphism F′ → TransformationP F F′
    UnliftMorphismPathP p .shape-path i s = p i .SymmetricContainerMorphism.shape-mor (s , BG.⋆) .fst
    UnliftMorphismPathP p .conjugator₀ s = {! !}
    UnliftMorphismPathP p .conjugator₁ = {! !}
    UnliftMorphismPathP p .conjugator-path i s = {!p i0 .SymmetricContainerMorphism.shape-mor (s , BG.⋆) .snd !}
    UnliftMorphismPathP p .is-conjugate = {! !}
    UnliftMorphismPathP p .is-pos-equiv = {! !}
