module GpdCont.LiftEquiv where

open import GpdCont.Prelude hiding (Lift)

open import GpdCont.QuotientContainer as QC using (QCont)
open import GpdCont.GroupoidContainer as GC using (GCont)
open import GpdCont.Univalence using (ua ; ua→)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma.Properties as Sigma using (ΣPathP)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

opaque
  -- Each endo-map on hGroupoids can be truncated to one on hSets.
  Tr : ∀ {ℓ} (F : hGroupoid ℓ → hGroupoid ℓ) → (hSet ℓ → hSet ℓ)
  Tr F (X , is-set-X) .fst = ∥ ⟨ F (X , isSet→isGroupoid is-set-X) ⟩ ∥₂
  Tr F (X , is-set-X) .snd = ST.isSetSetTrunc

{-
module EvalLift {ℓ} (Q : QCont ℓ) where
  open import GpdCont.Lift hiding (module LiftΣ)
  open import Cubical.Foundations.Isomorphism as Isomorphism using (Iso)
  open import Cubical.HITs.SetQuotients as SQ using (_/_)
  open QCont Q using (Shape ; Pos ; Symm ; _∼_ ; isTransSymm ; PosSet)

  open QC.Eval Q using (_∼*_) renaming (⟦_⟧ to ⟦Q⟧ ; ⟦_⟧ᵗ to ⟦Q⟧ᵗ)
  opaque
    -- Trᵗ : (F : Type ℓ → Type ℓ) → (hSet ℓ → hSet ℓ)
    -- Trᵗ F X .fst = ∥ F ⟨ X ⟩ ∥₂
    -- Trᵗ F X .snd = ST.isSetSetTrunc

    -- Each endo-map on hGroupoids can be truncated to one on hSets.
    Tr : (F : hGroupoid ℓ → hGroupoid ℓ) → (hSet ℓ → hSet ℓ)
    Tr F (X , is-set-X) .fst = ∥ ⟨ F (X , isSet→isGroupoid is-set-X) ⟩ ∥₂
    Tr F (X , is-set-X) .snd = ST.isSetSetTrunc

  -- Ext : (F : hGroupoid ℓ → hSet ℓ) → (hGroupoid ℓ → hGroupoid ℓ)
  -- Ext F X .fst = ⟨ F X ⟩
  -- Ext F X .snd = isSet→isGroupoid (str (F X))

  ↑Q : GCont ℓ
  ↑Q = Lift.↑ Q

  open Lift Q using (↑[_] ; ↑//)

  Tr⟦↑Q⟧ : hSet ℓ → hSet ℓ
  Tr⟦↑Q⟧ = Tr GC.Eval.⟦ ↑Q ⟧

  Tr⟦↑Q⟧ᵗ : hSet ℓ → Type ℓ
  Tr⟦↑Q⟧ᵗ X = ∥ GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ ∥₂

  opaque
    unfolding Tr GC.Eval.⟦_⟧
    _ : ∀ X → Tr⟦↑Q⟧ᵗ X ≡ ⟨ Tr GC.Eval.⟦ ↑Q ⟧ X ⟩
    _ = λ X → refl

  isSet-Tr⟦↑Q⟧ᵗ : ∀ X → isSet (Tr⟦↑Q⟧ᵗ X)
  isSet-Tr⟦↑Q⟧ᵗ X = ST.isSetSetTrunc

  opaque
    unfolding QC.Eval.⟦_⟧ᵗ
    to : (X : hSet _) → (⟦Q⟧ᵗ ⟨ X ⟩) → Tr⟦↑Q⟧ᵗ X
    to X (s , v) = SQ.rec (isSet-Tr⟦↑Q⟧ᵗ X) [_]* [-]*-well-defined v where
      module _ (v : Pos s → ⟨ X ⟩) where
        opaque
          unfolding Lift.↑Shape Lift.↑Pos
          ↑s : Lift.↑Shape Q
          ↑s = ↑[ s ]

          _ : Lift.↑Pos Q ↑s ≡ Pos s
          _ = refl

          ↑v : Lift.↑Pos Q ↑s → ⟨ X ⟩
          ↑v = v
          
        opaque
          unfolding GC.Eval.⟦_⟧ᵗ ↑s
          [↑_] : GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩
          [↑_] .fst = ↑s
          [↑_] .snd = ↑v

      [_]* : (v : Pos s → ⟨ X ⟩) → Tr⟦↑Q⟧ᵗ X
      [ v ]* = ST.∣ [↑ v ] ∣₂

      opaque
        unfolding _∼*_
          [↑_]
          [_]*
          GC.Eval.⟦_⟧ᵗ
          GC.Eval.label
          ua

        [↑-]-path : (v w : Pos s → ⟨ X ⟩)
          → (v ∼* w)
          → [↑ v ] ≡ [↑ w ]
        [↑-]-path v w (σ , is-symm-σ , σ-rel-v-w) = GC.Eval.⟦-⟧ᵗ-Path ↑Q α σ-rel-v-w where
          α : ↑[ s ] ≡ ↑[ s ]
          α = ↑// (σ , is-symm-σ)

        [-]*-well-defined : (v w : Pos s → ⟨ X ⟩) → v ∼* w → [ v ]* ≡ [ w ]*
        [-]*-well-defined v w r = cong ST.∣_∣₂ ([↑-]-path v w r)

  opaque
    unfolding GC.Eval.⟦_⟧ᵗ ⟦Q⟧ᵗ Lift.↑Shape Lift.↑Pos
    from″ : (X : hSet _) → GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ → (⟦Q⟧ᵗ ⟨ X ⟩)
    from″ X = uncurry (Lift.↑Shape-elimSet′ Q isInjPos isSetΠ⟦Q⟧ [_]* coherence) where
      isSetΠ⟦Q⟧ : ∀ ↑s → isSet ((GCont.Pos ↑Q ↑s → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩)
      isSetΠ⟦Q⟧ ↑s = isSetΠ (λ ↑v → QC.Eval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩)

      isInjPos : ∀ {s t} → Pos s ≃ Pos t → s ≡ t
      isInjPos = {! !}

      [_]* : (s : Shape) → (v : Pos s → ⟨ X ⟩) → Σ[ s ∈ Shape ] ((Pos s → ⟨ X ⟩) / _∼*_)
      [ s ]* v .fst = s
      [ s ]* v .snd = SQ.[ v ]

      coherence : ∀ {s} → (σ : s ∼ s) → PathP (λ i → (↑Q .GCont.Pos (↑// σ i) → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩) [ s ]* [ s ]*
      coherence {s} σ = funExtDep λ { {x₀ = v} {x₁ = w} p → ΣPathP (isInjPos (σ .fst) , toPathP (SQ.eq/ {! !} {! !} {!p !})) }
    from′ : (X : hSet _) → GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ → (⟦Q⟧ᵗ ⟨ X ⟩)
    from′ X = uncurry (Lift.↑Shape-elimSet Q isSetΠ⟦Q⟧ [_]* coherence) where
      isSetΠ⟦Q⟧ : ∀ ↑s → isSet ((GCont.Pos ↑Q ↑s → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩)
      isSetΠ⟦Q⟧ ↑s = isSetΠ (λ ↑v → QC.Eval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩)

      [_]* : (s : Shape) → (v : Pos s → ⟨ X ⟩) → Σ[ s ∈ Shape ] ((Pos s → ⟨ X ⟩) / _∼*_)
      [ s ]* v .fst = s
      [ s ]* v .snd = SQ.[ v ]

      -- TODO: Does this require injectivity of Pos?
      coherence : ∀ {s t} → (σ : s ∼ t) → PathP (λ i → (↑Q .GCont.Pos (↑// σ i) → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩) [ s ]* [ t ]*
      coherence σ = funExtDep λ { {x₀ = v} {x₁ = w} p → ΣPathP ({! !} , {! !}) }

  from : (X : hSet _) → Tr⟦↑Q⟧ᵗ X → (⟦Q⟧ᵗ ⟨ X ⟩)
  from X = ST.rec (QC.Eval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩) (from′ X)

  opaque
    unfolding QC.Eval.⟦_⟧ GC.Eval.⟦_⟧
    ι : ∀ (X : hSet ℓ)
      → Iso (⟦Q⟧ᵗ ⟨ X ⟩) (Tr⟦↑Q⟧ᵗ X)
    ι X .Iso.fun = to X
    ι X .Iso.inv = {!from !}
    ι X .Iso.rightInv = {! !}
    ι X .Iso.leftInv = {! !}
    lemma : ∀ (X : hSet ℓ)
      → (Σ[ s ∈ Shape ] (Pos s → ⟨ X ⟩) / _∼*_) ≃ ∥ GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ ∥₂
    lemma X = Isomorphism.isoToEquiv (ι X)

  opaque
    unfolding QC.Eval.⟦_⟧ Tr GC.Eval.⟦_⟧
    thm : ∀ X → ⟨ ⟦Q⟧ X ⟩ ≃ ⟨ Tr⟦↑Q⟧ X ⟩
    thm X =
      Σ[ s ∈ Shape ] (Pos s → ⟨ X ⟩) / _∼*_ ≃⟨ lemma X ⟩
      ∥ GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ ∥₂ ≃∎

  cor : ∀ X → ⟦Q⟧ X ≡ Tr⟦↑Q⟧ X
  cor X = TypeOfHLevel≡ 2 (ua $ thm X)

module EvalLiftΣ {ℓ} (Q : QCont ℓ) where
  open import GpdCont.Lift hiding (module Lift)
  open import Cubical.Foundations.Isomorphism as Isomorphism using (Iso)
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
  open import Cubical.HITs.SetQuotients as SQ using (_/_)
  open QCont Q using (Shape ; Pos ; Symm ; _∼_ ; isTransSymm ; PosSet)
  module Q = QCont Q

  open QC.Eval Q using (_∼*_ ; ∼*→∼ ; _∼*⁻¹) renaming (⟦_⟧ to ⟦Q⟧ ; ⟦_⟧ᵗ to ⟦Q⟧ᵗ)
  opaque
    -- Each endo-map on hGroupoids can be truncated to one on hSets.
    Tr : (F : hGroupoid ℓ → hGroupoid ℓ) → (hSet ℓ → hSet ℓ)
    Tr F (X , is-set-X) .fst = ∥ ⟨ F (X , isSet→isGroupoid is-set-X) ⟩ ∥₂
    Tr F (X , is-set-X) .snd = ST.isSetSetTrunc

  ↑Q : GCont ℓ
  ↑Q = LiftΣ.↑ Q

  module ↑Q = LiftΣ Q
  open LiftΣ Q using (↑Shape ; ↑Pos)

  Tr⟦↑Q⟧ : hSet ℓ → hSet ℓ
  Tr⟦↑Q⟧ = Tr GC.Eval.⟦ ↑Q ⟧

  Tr⟦↑Q⟧ᵗ : hSet ℓ → Type ℓ
  Tr⟦↑Q⟧ᵗ X = ∥ GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ ∥₂

  opaque
    unfolding Tr GC.Eval.⟦_⟧
    _ : ∀ X → Tr⟦↑Q⟧ᵗ X ≡ ⟨ Tr GC.Eval.⟦ ↑Q ⟧ X ⟩
    _ = λ X → refl

  isSet-Tr⟦↑Q⟧ᵗ : ∀ X → isSet (Tr⟦↑Q⟧ᵗ X)
  isSet-Tr⟦↑Q⟧ᵗ X = ST.isSetSetTrunc

  module ⟦↑Q⟧ = GC.Eval ↑Q
    renaming (⟦-⟧ᵗ-Path to ᵗ-Path)

  opaque
    unfolding Tr QC.Eval.⟦_⟧ᵗ GC.Eval.⟦_⟧ᵗ _∼*_
    to : (X : hSet _) → (⟦Q⟧ᵗ ⟨ X ⟩) → Tr⟦↑Q⟧ᵗ X
    to X (s , v) = SQ.rec (isSet-Tr⟦↑Q⟧ᵗ X) [_]* [-]*-well-defined v where
      [_]* : (v : Pos s → ⟨ X ⟩) → Tr⟦↑Q⟧ᵗ X
      [ v ]* = ST.∣ GC.Eval.mk⟦ ↑Q ⟧ᵗ (↑Q.↑shape s , v) ∣₂

      [-]*-well-defined : (v w : Pos s → ⟨ X ⟩) → v ∼* w → [ v ]* ≡ [ w ]*
      [-]*-well-defined v w r = cong ST.∣_∣₂ (⟦↑Q⟧.ᵗ-Path shape-loop {! !}) where
        shape-loop : ↑Q.↑shape s ≡ ↑Q.↑shape s
        shape-loop = ↑Q.↑ShapeLoop (∼*→∼ r)

        shape-loop′ : ↑Q.↑shape s ≡ ↑Q.↑shape s
        shape-loop′ = ↑Q.↑ShapeLoop (∼*→∼ (r ∼*⁻¹))

        coh : ua (r .fst) ≡ refl
        coh = {! !}

        -- fun-path : PathP (λ i → ua (r .fst) i → ⟨ X ⟩) v w
        -- fun-path = r .snd .snd

        label-path′ : v ≡ w
        label-path′ = funExt {! !}

        label-path : PathP (λ i → Pos s → ⟨ X ⟩) v w
        label-path = funExtDep
          λ { {x₀} {x₁} → λ (p : x₀ ≡ x₁) →
            v x₀ ≡⟨ funExtDep⁻ (r .snd .snd) {x₀} {x₁} {!p!} ⟩
            w x₁ ∎
          }

      -- module _ (v : Pos s → ⟨ X ⟩) where
      --   opaque
      --     unfolding Lift.↑Shape Lift.↑Pos
      --     ↑s : Lift.↑Shape Q
      --     ↑s = ↑[ s ]

      --     _ : Lift.↑Pos Q ↑s ≡ Pos s
      --     _ = refl

      --     ↑v : Lift.↑Pos Q ↑s → ⟨ X ⟩
      --     ↑v = v
          
      --   opaque
      --     unfolding GC.Eval.⟦_⟧ᵗ ↑s
      --     [↑_] : GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩
      --     [↑_] .fst = ↑s
      --     [↑_] .snd = ↑v

      -- opaque
      --   unfolding _∼*_
      --     [↑_]
      --     [_]*
      --     GC.Eval.⟦_⟧ᵗ
      --     GC.Eval.label

      --   [↑-]-path : (v w : Pos s → ⟨ X ⟩)
      --     → (v ∼* w)
      --     → [↑ v ] ≡ [↑ w ]
      --   [↑-]-path v w (σ , is-symm-σ , σ-rel-v-w) = GC.Eval.⟦-⟧ᵗ-Path ↑Q α σ-rel-v-w where
      --     α : ↑[ s ] ≡ ↑[ s ]
      --     α = ↑// (σ , is-symm-σ)

  opaque
    unfolding GC.Eval.⟦_⟧ᵗ ⟦Q⟧ᵗ
    from′ : (X : hSet _) → GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ → (⟦Q⟧ᵗ ⟨ X ⟩)
    from′ X = uncurry {! !} where
      goal : (s : ↑Shape) → (v : ↑Pos s → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩
      goal = {! !}
    -- uncurry (Lift.↑Shape-elimSet Q isSetΠ⟦Q⟧ [_]* coherence) where
      -- isSetΠ⟦Q⟧ : ∀ ↑s → isSet ((GCont.Pos ↑Q ↑s → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩)
      -- isSetΠ⟦Q⟧ ↑s = isSetΠ (λ ↑v → QC.Eval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩)

      -- [_]* : (s : Shape) → (v : Pos s → ⟨ X ⟩) → Σ[ s ∈ Shape ] ((Pos s → ⟨ X ⟩) / _∼*_)
      -- [ s ]* v .fst = s
      -- [ s ]* v .snd = SQ.[ v ]

      -- -- TODO: Does this require injectivity of Pos?
      -- coherence : ∀ {s t} → (σ : s ∼ t) → PathP (λ i → (↑Q .GCont.Pos (↑// σ i) → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩) [ s ]* [ t ]*
      -- coherence σ = funExtDep λ { {x₀ = v} {x₁ = w} p → ΣPathP ({! !} , {! !}) }

  from : (X : hSet _) → Tr⟦↑Q⟧ᵗ X → (⟦Q⟧ᵗ ⟨ X ⟩)
  from X = ST.rec (QC.Eval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩) (from′ X)

  opaque
    unfolding QC.Eval.⟦_⟧ GC.Eval.⟦_⟧
    ι : ∀ (X : hSet ℓ)
      → Iso (⟦Q⟧ᵗ ⟨ X ⟩) (Tr⟦↑Q⟧ᵗ X)
    ι X .Iso.fun = to X
    ι X .Iso.inv = {!from !}
    ι X .Iso.rightInv = {! !}
    ι X .Iso.leftInv = {! !}
    lemma : ∀ (X : hSet ℓ)
      → (Σ[ s ∈ Shape ] (Pos s → ⟨ X ⟩) / _∼*_) ≃ ∥ GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ ∥₂
    lemma X = Isomorphism.isoToEquiv (ι X)

  opaque
    unfolding QC.Eval.⟦_⟧ Tr GC.Eval.⟦_⟧
    thm : ∀ X → ⟨ ⟦Q⟧ X ⟩ ≃ ⟨ Tr⟦↑Q⟧ X ⟩
    thm X =
      Σ[ s ∈ Shape ] (Pos s → ⟨ X ⟩) / _∼*_ ≃⟨ lemma X ⟩
      ∥ GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ ∥₂ ≃∎

  cor : ∀ X → ⟦Q⟧ X ≡ Tr⟦↑Q⟧ X
  cor X = TypeOfHLevel≡ 2 (ua $ thm X)

-}

module EvalLiftLoop {ℓ} (Q : QCont ℓ) where
  open import GpdCont.Lift hiding (module Lift)
  open import Cubical.Foundations.Isomorphism as Isomorphism using (Iso)
  open import Cubical.HITs.SetQuotients as SQ using (_/_)
  open QCont Q using (Shape ; Pos ; Symm ; _∼_ ; isTransSymm ; PosSet)
  module Q = QCont Q

  open QC.Eval Q using (_∼*_ ; ∼*→∼ ; _∼*⁻¹) renaming (⟦_⟧ to ⟦Q⟧ ; ⟦_⟧ᵗ to ⟦Q⟧ᵗ)

  ↑Q : GCont ℓ
  ↑Q = LiftLoop.↑ Q

  module ↑Q = LiftLoop Q
  open LiftLoop Q using (↑Shape ; ↑Pos)

  Tr⟦↑Q⟧ : hSet ℓ → hSet ℓ
  Tr⟦↑Q⟧ = Tr GC.Eval.⟦ ↑Q ⟧

  Tr⟦↑Q⟧ᵗ : hSet ℓ → Type ℓ
  Tr⟦↑Q⟧ᵗ X = ∥ GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ ∥₂

  opaque
    unfolding Tr GC.Eval.⟦_⟧
    _ : ∀ X → Tr⟦↑Q⟧ᵗ X ≡ ⟨ Tr GC.Eval.⟦ ↑Q ⟧ X ⟩
    _ = λ X → refl

  isSet-Tr⟦↑Q⟧ᵗ : ∀ X → isSet (Tr⟦↑Q⟧ᵗ X)
  isSet-Tr⟦↑Q⟧ᵗ X = ST.isSetSetTrunc

  module LiftTruncEquiv (X : hSet ℓ) where
    module ⟦↑Q⟧ = GC.Eval ↑Q
      renaming (⟦-⟧ᵗ-Path to ᵗ-Path ; ⟦_⟧ᵗ to ᵗ)

    opaque
      unfolding Tr QC.Eval.⟦_⟧ᵗ GC.Eval.⟦_⟧ᵗ _∼*_ ↑Pos ua
      to-lift-trunc : (⟦Q⟧ᵗ ⟨ X ⟩) → Tr⟦↑Q⟧ᵗ X
      to-lift-trunc (s , v) = SQ.rec (isSet-Tr⟦↑Q⟧ᵗ X) [_]* [-]*-well-defined v where
        [_]* : (v : Pos s → ⟨ X ⟩) → Tr⟦↑Q⟧ᵗ X
        [ v ]* = ST.∣ GC.Eval.mk⟦ ↑Q ⟧ᵗ (↑Q.↑shape s , v) ∣₂

        [-]*-well-defined : (v w : Pos s → ⟨ X ⟩) → v ∼* w → [ v ]* ≡ [ w ]*
        [-]*-well-defined v w r = cong ST.∣_∣₂ (⟦↑Q⟧.ᵗ-Path shape-loop label-path) where
          shape-loop : ↑Q.↑shape s ≡ ↑Q.↑shape s
          shape-loop = ↑Q.↑loop (∼*→∼ r)

          label-path : PathP (λ i → ↑Q.↑Pos (shape-loop i) → ⟨ X ⟩) v w
          label-path = r .snd .snd

    opaque
      unfolding GC.Eval.⟦_⟧ᵗ ⟦Q⟧ᵗ ↑Pos _∼*_ ua
      from-lift : GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ → (⟦Q⟧ᵗ ⟨ X ⟩)
      from-lift = uncurry goal where
        isSetΠ⟦Q⟧ : ∀ ↑s → isSet ((GCont.Pos ↑Q ↑s → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩)
        isSetΠ⟦Q⟧ ↑s = isSetΠ (λ ↑v → QC.Eval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩)

        [_]* : (s : Shape) → (v : Pos s → ⟨ X ⟩) → Σ[ s ∈ Shape ] ((Pos s → ⟨ X ⟩) / _∼*_)
        [ s ]* = QC.Eval.Label→⟦ Q ⟧ᵗ

        coherence : ∀ {s} → (σ : s ∼ s) → PathP (λ i → (ua (σ .fst) i → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩) [ s ]* [ s ]*
        coherence {s} σ = funExtDep λ { {x₀ = v} {x₁ = w} p → ΣPathP (refl , SQ.eq/ v w (σ .fst , σ .snd , p)) }

        goal : (s : ↑Shape) → (v : ↑Pos s → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩
        goal = ↑Q.↑Shape-elimSet (λ {a0} {a1} → isOfHLevel→isOfHLevelDep 2 isSetΠ⟦Q⟧ {a0} {a1}) [_]* coherence

    from-lift-trunc : Tr⟦↑Q⟧ᵗ X → (⟦Q⟧ᵗ ⟨ X ⟩)
    from-lift-trunc = ST.rec (QC.Eval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩) from-lift

    opaque
      unfolding ⟦Q⟧ᵗ from-lift to-lift-trunc ↑Pos
      lift-trunc-rightInv : ∀ (x : Tr⟦↑Q⟧ᵗ X) → to-lift-trunc (from-lift-trunc x) ≡ x
      lift-trunc-rightInv = ST.elim (isProp→isSet ∘ isPropPath) goal where
        isPropPath : ∀ x → isProp (to-lift-trunc (from-lift-trunc x) ≡ x)
        isPropPath x = ST.isSetSetTrunc _ x

        workhorse : (s : Shape) (v : Pos s → ⟨ X ⟩) → to-lift-trunc (from-lift-trunc ST.∣ ↑Q.↑shape s , v ∣₂) ≡ ST.∣ ↑Q.↑shape s , v ∣₂
        workhorse s v = refl

        lemma : ∀ (s : ↑Shape) (v : ↑Pos s → ⟨ X ⟩) → to-lift-trunc (from-lift-trunc ST.∣ (s , v) ∣₂) ≡ ST.∣ (s , v) ∣₂
        lemma = ↑Q.↑Shape-elimProp (λ s → isPropΠ λ v → isPropPath ST.∣ s , v ∣₂) workhorse

        goal : ∀ (x : ⟦↑Q⟧.ᵗ ⟨ X ⟩) → to-lift-trunc (from-lift-trunc ST.∣ x ∣₂) ≡ ST.∣ x ∣₂
        goal = uncurry lemma

    opaque
      unfolding ⟦Q⟧ᵗ from-lift to-lift-trunc
      lift-trunc-leftInv : ∀ (x : ⟦Q⟧ᵗ ⟨ X ⟩) → (from-lift-trunc (to-lift-trunc x)) ≡ x
      lift-trunc-leftInv (s , v) = SQ.elimProp {P = Motive} isPropMotive [_]* v where
        Motive : ∀ (v : (Pos s → ⟨ X ⟩) / _∼*_) → Type ℓ
        Motive v = from-lift-trunc (to-lift-trunc (s , v)) ≡ (s , v)

        isPropMotive : ∀ v → isProp (Motive v)
        isPropMotive v = QC.Eval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩ _ (s , v)

        [_]* : (v : Pos s → ⟨ X ⟩) → Motive SQ.[ v ]
        [ v ]* = refl

    lift-trunc-Iso : Iso (⟦Q⟧ᵗ ⟨ X ⟩) (Tr⟦↑Q⟧ᵗ X)
    lift-trunc-Iso .Iso.fun = to-lift-trunc
    lift-trunc-Iso .Iso.inv = from-lift-trunc
    lift-trunc-Iso .Iso.rightInv = lift-trunc-rightInv
    lift-trunc-Iso .Iso.leftInv = lift-trunc-leftInv

  opaque
    unfolding QC.Eval.⟦_⟧ GC.Eval.⟦_⟧
    lemma : ∀ (X : hSet ℓ)
      → (Σ[ s ∈ Shape ] (Pos s → ⟨ X ⟩) / _∼*_) ≃ ∥ GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ ∥₂
    lemma X = Isomorphism.isoToEquiv (LiftTruncEquiv.lift-trunc-Iso X)

  opaque
    unfolding QC.Eval.⟦_⟧ Tr GC.Eval.⟦_⟧
    thm : ∀ X → ⟨ ⟦Q⟧ X ⟩ ≃ ⟨ Tr⟦↑Q⟧ X ⟩
    thm X =
      Σ[ s ∈ Shape ] (Pos s → ⟨ X ⟩) / _∼*_ ≃⟨ lemma X ⟩
      ∥ GC.Eval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ ∥₂ ≃∎

  cor : ∀ X → ⟦Q⟧ X ≡ Tr⟦↑Q⟧ X
  cor X = TypeOfHLevel≡ 2 (ua $ thm X)
