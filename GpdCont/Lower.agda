module GpdCont.Lower where

open import GpdCont.Prelude

open import GpdCont.QuotientContainer as QC using (QCont)
open import GpdCont.GroupoidContainer as GC using (GCont)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

module BoolExample where
  open import Cubical.Data.Bool
  open import Cubical.Functions.Involution

  data 𝔹2 : Type where
    ⋆ : 𝔹2
    swap : ⋆ ≡ ⋆
    mul : compSquareFiller swap swap refl
    trunc𝔹2 : isGroupoid 𝔹2

  rec : ∀ {ℓ} {B : Type ℓ}
    → (isGroupoid B)
    → (b : B)
    → (p : b ≡ b)
    → (p² : p ∙ p ≡ refl)
    → 𝔹2 → B
  rec {B} is-gpd-B b p p² = go where
    go : _ → _
    go ⋆ = b
    go (swap i) = p i
    go (mul i j) = goal i j where
      goal : compSquareFiller p p refl
      goal = coerceCompSquareFiller p²
    go (trunc𝔹2 x y p q r s i j k) = is-gpd-B (go x) (go y) (cong go p) (cong go q) (cong (cong go) r) (cong (cong go) s) i j k

  PosSet : 𝔹2 → hSet _
  PosSet = rec isGroupoidHSet (Bool , isSetBool) (TypeOfHLevel≡ 2 notEq) (ΣSquareSet (λ X → isProp→isSet isPropIsSet) (involPathComp notnot))

  Pos : 𝔹2 → Type
  Pos = ⟨_⟩ ∘ PosSet

  𝔹 : GCont _
  𝔹 .GCont.Shape = 𝔹2
  𝔹 .GCont.Pos = Pos
  𝔹 .GCont.is-groupoid-shape = trunc𝔹2
  𝔹 .GCont.is-set-pos = str ∘ PosSet

module Lower {ℓ} (G : GCont ℓ) (injPos : ∀ s t → G .GCont.Pos s ≡ G .GCont.Pos t → s ≡ t) where
  open module G = GCont G using (Shape ; is-groupoid-shape ; Pos ; is-set-pos)

  opaque
    ↓Shape : Type ℓ
    ↓Shape = ∥ Shape ∥₂

    isSet-↓Shape : isSet ↓Shape
    isSet-↓Shape = ST.isSetSetTrunc

    -- False lmao
    ↓pos-coherence : ∀ (s t : Shape) → (p q : s ≡ t) → Path (G.Pos s ≡ G.Pos t) (cong G.Pos p) (cong G.Pos q)
    ↓pos-coherence s t p q = {! !}

    ↓PosSet : ↓Shape → hSet ℓ
    ↓PosSet = Rec.fun where
      opaque
        unfolding G.PosSet
        coherence : ∀ (s t : Shape) → (p q : s ≡ t) → Path (G.PosSet s ≡ G.PosSet t) (cong G.PosSet p) (cong G.PosSet q)
        coherence s t p q = ΣSquareSet (λ X → isProp→isSet isPropIsSet) (↓pos-coherence s t p q)
      module Rec = ST.rec→Gpd isGroupoidHSet G.PosSet coherence

    ↓Pos : ↓Shape → Type ℓ
    ↓Pos = ⟨_⟩ ∘ ↓PosSet

    isSet-↓Pos : (s : ↓Shape) → isSet (↓Pos s)
    isSet-↓Pos = str ∘ ↓PosSet

    ↓Symm′ : ∀ {s t} → ↓Pos s ≃ ↓Pos t → hProp ℓ
    ↓Symm′ {s} {t} σ = {! !}

    ↓Symm : ∀ {s t} → ↓Pos s ≃ ↓Pos t → Type ℓ
    ↓Symm {s} {t} = ⟨_⟩ ∘ ↓Symm′ {s} {t}

    isProp-↓Symm : ∀ {s t} → (σ : ↓Pos s ≃ ↓Pos t) → isProp (↓Symm σ)
    isProp-↓Symm {s} {t} = str ∘ ↓Symm′ {s} {t}

  ↓_ : QCont ℓ
  ↓ .QCont.Shape = ↓Shape
  ↓ .QCont.Pos = ↓Pos
  ↓ .QCont.Symm = ↓Symm
  ↓ .QCont.is-set-shape = isSet-↓Shape
  ↓ .QCont.is-set-pos = isSet-↓Pos
  ↓ .QCont.is-prop-symm = isProp-↓Symm
  ↓ .QCont.symm-comp = {! !}
{-
open import GpdCont.Partition
module Lower' {ℓ} (G : GCont ℓ) (π : Partition (G .GCont.Shape)) where
  open module G = GCont G using
    (Shape ; is-groupoid-shape ; Pos ; is-set-pos ; PosSet)

  open Partition π
    using (Idx ; part-equiv)
    renaming (Part to ShapePart ; pt to shape·)

  ↓Shape : Type ℓ
  ↓Shape = Idx

  ↓PosSet : ↓Shape → hSet ℓ
  ↓PosSet = PosSet ∘ shape·

  opaque
    unfolding PosSet
    isSet-↓Shape : isSet ↓Shape
    isSet-↓Shape = π .Partition.is-set-idx

    ↓Pos : ↓Shape → Type ℓ
    ↓Pos = ⟨_⟩ ∘ ↓PosSet

    isSet-↓Pos : (s : ↓Shape) → isSet (↓Pos s)
    isSet-↓Pos = str ∘ ↓PosSet

    ↓Symm≡ : ∀ {s t} → ↓Pos s ≡ ↓Pos t → hProp ℓ
    ↓Symm≡ {s} {t} p = {! !} where
      Pos′ : Type ℓ
      Pos′ = Pos (shape· s)

    ↓Symm′ : ∀ {s t} → ↓Pos s ≃ ↓Pos t → hProp ℓ
    ↓Symm′ {s} {t} σ = ↓Symm≡ (ua σ)

    ↓Symm : ∀ {s t} → ↓Pos s ≃ ↓Pos t → Type ℓ
    ↓Symm {s} {t} = ⟨_⟩ ∘ ↓Symm′ {s} {t}

    isProp-↓Symm : ∀ {s t} → (σ : ↓Pos s ≃ ↓Pos t) → isProp (↓Symm σ)
    isProp-↓Symm {s} {t} = str ∘ ↓Symm′ {s} {t}

  ↓_ : QCont ℓ
  ↓ .QCont.Shape = ↓Shape
  ↓ .QCont.Pos = ↓Pos
  ↓ .QCont.Symm = ↓Symm
  ↓ .QCont.is-set-shape = isSet-↓Shape
  ↓ .QCont.is-set-pos = isSet-↓Pos
  ↓ .QCont.is-prop-symm = isProp-↓Symm
  ↓ .QCont.is-equiv-rel-symm = {! !}

open import GpdCont.IterativeSets
open import Cubical.Functions.Image
module LowerV {ℓ} (G : GCont ℓ) (is-iterative-set-pos : ∀ s → isInImage El⁰ (G .GCont.Pos s)) where
  open module G = GCont G using (Shape ; is-groupoid-shape ; Pos ; is-set-pos)

  opaque
    ↓Shape : Type ℓ
    ↓Shape = ∥ Shape ∥₂

    isSet-↓Shape : isSet ↓Shape
    isSet-↓Shape = ST.isSetSetTrunc

    ↓PosV : ↓Shape → V⁰ ℓ
    ↓PosV = ST.rec isSetV⁰ PosV where
      coherence : ∀ {s} (x y : fiber El⁰ (Pos s)) → x .fst ≡ y .fst
      coherence (x , El⁰x≡Pos-s) (y , El⁰y≡Pos-s) = {! !}
      PosV : Shape → V⁰ ℓ
      PosV s = PT.elim→Set {A = fiber El⁰ (Pos s)} (λ _ → isSetV⁰) fst {! !} (is-iterative-set-pos s)

    ↓PosSet : ↓Shape → hSet ℓ
    ↓PosSet = V⁰→hSet ∘ ↓PosV

    ↓Pos : ↓Shape → Type ℓ
    ↓Pos = ⟨_⟩ ∘ ↓PosSet

    isSet-↓Pos : (s : ↓Shape) → isSet (↓Pos s)
    isSet-↓Pos = str ∘ ↓PosSet

    ↓Symm′ : ∀ {s t} → ↓Pos s ≃ ↓Pos t → hProp ℓ
    ↓Symm′ {s} {t} σ = {! !}

    ↓Symm : ∀ {s t} → ↓Pos s ≃ ↓Pos t → Type ℓ
    ↓Symm {s} {t} = ⟨_⟩ ∘ ↓Symm′ {s} {t}

    isProp-↓Symm : ∀ {s t} → (σ : ↓Pos s ≃ ↓Pos t) → isProp (↓Symm σ)
    isProp-↓Symm {s} {t} = str ∘ ↓Symm′ {s} {t}

  ↓_ : QCont ℓ
  ↓ .QCont.Shape = ↓Shape
  ↓ .QCont.Pos = ↓Pos
  ↓ .QCont.Symm = ↓Symm
  ↓ .QCont.is-set-shape = isSet-↓Shape
  ↓ .QCont.is-set-pos = isSet-↓Pos
  ↓ .QCont.is-prop-symm = isProp-↓Symm
  ↓ .QCont.is-equiv-rel-symm = {! !}

-}
