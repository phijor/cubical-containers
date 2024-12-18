open import GpdCont.Prelude
open import GpdCont.ActionContainer.Base
open import GpdCont.GroupAction.Equivariant using (isEquivariantMap[_][_,_])

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (isPropIsGroupHom)

module GpdCont.ActionContainer.Morphism {ℓ} (C D : ActionContainer ℓ) where
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

  isEquivariantPosMap : {u : S → T} (f : ∀ s → Q (u s) → P s) (φ : ∀ s → G s → H (u s)) → Type ℓ
  isEquivariantPosMap f φ = ∀ (s : S) (g : G s) → equivFun (σ g) ∘ f s ≡ f s ∘ equivFun (τ (φ s g))

  isSymmGroupHom : {u : S → T} (φ : ∀ s → G s → H (u s)) → Type ℓ
  isSymmGroupHom {u} φ = ∀ (s : S) → IsGroupHom (C.symm-group-str s) (φ s) (D.symm-group-str (u s))

  isPropIsSymmGroupHom : ∀ {u} {φ} → isProp (isSymmGroupHom {u} φ)
  isPropIsSymmGroupHom = isPropΠ λ s → isPropIsGroupHom _ _

  record Morphismᴰ (shape-map : S → T) : Type ℓ where
    constructor mkMorphismᴰ
    field
      pos-map : ∀ s → Q (shape-map s) → P s
      symm-map : ∀ s → G s → H (shape-map s)

    field
      is-group-hom-symm-map : isSymmGroupHom symm-map
      is-equivariant-pos-map : isEquivariantPosMap pos-map symm-map

    symm-hom : ∀ s → GroupHom (C.SymmGroup s) (D.SymmGroup $ shape-map s)
    symm-hom s .fst = symm-map s
    symm-hom s .snd = is-group-hom-symm-map s

    is-equivariant-pos-map' : ∀ s → isEquivariantMap[ symm-hom s , pos-map s ][ C.symmAction s , D.symmAction (shape-map s) ]
    is-equivariant-pos-map' = is-equivariant-pos-map

  unquoteDecl MorphismᴰIsoΣ = declareRecordIsoΣ MorphismᴰIsoΣ (quote Morphismᴰ)

  instance
    MorphismᴰToΣ : ∀ {u} → RecordToΣ (Morphismᴰ u)
    MorphismᴰToΣ = toΣ MorphismᴰIsoΣ

  opaque
    isSetMorphismᴰ : ∀ u → isSet (Morphismᴰ u)
    isSetMorphismᴰ u = recordIsOfHLevel 2 $ isSetΣ
      (isSetΠ2 (λ _ _ → C.is-set-pos _))
      λ f → isSetΣ
        (isSetΠ2 (λ _ _ → D.isSetSymm (u _)))
        λ φ → isProp→isSet (isProp× isPropIsSymmGroupHom (isPropΠ2 λ s g → isSet→ (C.is-set-pos s) _ _))

  record Morphism : Type ℓ where
    constructor _▷[_]
    field
      shape-map : S → T
      mor-str : Morphismᴰ shape-map

    open Morphismᴰ mor-str public

  unquoteDecl MorphismIsoΣ = declareRecordIsoΣ MorphismIsoΣ (quote Morphism)

  instance
    MorphismToΣ : RecordToΣ Morphism
    MorphismToΣ = toΣ MorphismIsoΣ

  opaque
    isSetMorphism : isSet Morphism
    isSetMorphism = recordIsOfHLevel 2 $ isSetΣ (isSet→ D.is-set-shape) isSetMorphismᴰ

  open Morphismᴰ
  open Morphism

  mkMorphism : (u : S → T) (f : ∀ s → Q (u s) → P s) (φ : ∀ s → G s → H (u s))
    → isEquivariantPosMap f φ
    → isSymmGroupHom φ
    → Morphism
  mkMorphism u f φ is-equivariant-f is-group-hom-φ = λ where
    .shape-map → u
    .mor-str .pos-map → f
    .mor-str .symm-map → φ
    .mor-str .is-equivariant-pos-map → is-equivariant-f
    .mor-str .is-group-hom-symm-map → is-group-hom-φ

  mkMorphism-syntax : (u : S → T) (φ : ∀ s → GroupHom (C.SymmGroup s) (D.SymmGroup (u s))) (f : Σ[ f ∈ _ ] isEquivariantPosMap f (fst ∘ φ))
    → Morphism
  mkMorphism-syntax u φ f = mkMorphism u (f .fst) (fst ∘ φ) (f .snd) (snd ∘ φ)

  syntax mkMorphism-syntax u φ f = u ▷ f ◁ φ

  mkMorphismBundled : (u : S → T)
    → (φ : ∀ s → GroupHom (C.SymmGroup s) (D.SymmGroup (u s)))
    → Σ[ f ∈ (∀ s → Q (u s) → P s) ] isEquivariantPosMap f (fst ∘ φ)
    → Morphism
  mkMorphismBundled u φ (f , is-equivariant-f) = mkMorphism u f (fst ∘ φ) is-equivariant-f (snd ∘ φ)

  Morphism≡ : {f g : Morphism}
    → (shape : f .shape-map ≡ g .shape-map)
    → (pos : PathP (λ i → ∀ s → Q (shape i s) → P s) (f .pos-map) (g .pos-map))
    → PathP (λ i → ∀ s → G s → H (shape i s)) (f .symm-map) (g .symm-map)
    → f ≡ g
  Morphism≡ shape pos symm i .shape-map = shape i
  Morphism≡ shape pos symm i .mor-str .pos-map = pos i
  Morphism≡ shape pos symm i .mor-str .symm-map = symm i
  Morphism≡ shape pos symm i .mor-str .is-group-hom-symm-map = ? -- isProp→PathP (λ _ → isPropIsSymmGroupHom) (f .is-group-hom-symm-map) (g .is-group-hom-symm-map) i
  Morphism≡ shape pos symm i .mor-str .is-equivariant-pos-map = ? -- isProp→PathP {! !}
