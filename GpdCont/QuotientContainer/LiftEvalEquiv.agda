module GpdCont.QuotientContainer.LiftEvalEquiv where

open import GpdCont.Prelude hiding (Lift)

open import GpdCont.QuotientContainer.Base using (QCont)
open import GpdCont.Univalence using (ua ; ua→)
open import GpdCont.SetTruncation using (setTruncateFstΣ≃)

import GpdCont.QuotientContainer.Lift as Lift
import GpdCont.QuotientContainer.Eval as QCEval
import GpdCont.Coffin.Eval as CoffinEval

open import Cubical.Foundations.Equiv renaming (invEquiv to _⁻ᵉ)
open import Cubical.Foundations.Equiv.Properties using (cong≃)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism as Isomorphism using (Iso ; isoToEquiv) renaming (invIso to _⁻ⁱ)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma.Properties as Sigma using (ΣPathP)
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.SetQuotients as SQ using (_/_)

-- Each endo-map on hGroupoids can be truncated to one on hSets.
Tr : ∀ {ℓ} (F : hGroupoid ℓ → hGroupoid ℓ) → (hSet ℓ → hSet ℓ)
Tr F (X , is-set-X) .fst = ∥ ⟨ F (X , isSet→isGroupoid is-set-X) ⟩ ∥₂
Tr F (X , is-set-X) .snd = ST.isSetSetTrunc

isSetTr : ∀ {ℓ} (F : hGroupoid ℓ → hGroupoid ℓ) → ∀ X → isSet ⟨ Tr F X ⟩
isSetTr F X = str $ Tr F X

module EvalLiftLoop {ℓ} (Q : QCont ℓ) where
  import GpdCont.SymmetricContainer.Eval

  open module Q = QCont Q using (Shape ; Pos ; isSymm ; Symm ; PosSet)
  open module ⟦Q⟧ = QCEval Q using (_∼*_) renaming (⟦_⟧ to ⟦Q⟧ ; ⟦_⟧ᵗ to ⟦Q⟧ᵗ)

  open module ↑Q = Lift Q using (↑Shape ; ↑Pos ; ↑⟨_,_⟩ ; ↑Symm ; module ↑SymmElim) renaming (↑ to ↑Q)
  open module ⟦↑Q⟧ = CoffinEval ↑Q using () renaming (⟦_⟧ to ⟦↑Q⟧ ; ⟦_⟧ᵗ to ⟦↑Q⟧ᵗ ; ⟦-⟧ᵗ-Path to ⟦↑Q⟧ᵗ-Path)

  module LiftTruncEquiv (X : hSet ℓ) where
    opaque
      unfolding Q.PosPath CoffinEval.label
      to-lift-trunc : (⟦Q⟧ᵗ ⟨ X ⟩) → ⟨ Tr ⟦↑Q⟧ X ⟩
      to-lift-trunc = QCEval.⟦ Q ⟧ᵗ-rec (isSetTr ⟦↑Q⟧ X) [_]* [-]*-well-defined where
        [_]* : ∀ {s} (v : Pos s → ⟨ X ⟩) → ⟨ Tr ⟦↑Q⟧ X ⟩
        [ v ]* = ST.∣ CoffinEval.mk⟦ ↑Q ⟧ᵗ (↑Q.↑shape _ , v) ∣₂

        -- FIXME See below how to fix
        [-]*-well-defined : ∀ {s} (v w : Pos s → ⟨ X ⟩) → v ∼* w → [ v ]* ≡ [ w ]*
        [-]*-well-defined {s} v w r = cong ST.∣_∣₂ (⟦↑Q⟧ᵗ-Path shape-loop label-path) where
          shape-loop : ↑Q.↑shape s ≡ ↑Q.↑shape s
          shape-loop = ↑Q.↑loop {! !} -- (∼*→∼ r)

          label-path : PathP (λ i → ↑Q.↑Pos (shape-loop i) → ⟨ X ⟩) v w
          label-path = {! !} -- ∼*→PathP* r

      from-lift : CoffinEval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ → (⟦Q⟧ᵗ ⟨ X ⟩)
      from-lift = uncurry goal where
        isSetΠ⟦Q⟧ : ∀ ↑s → isSet ((↑Pos ↑s → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩)
        isSetΠ⟦Q⟧ ↑s = isSetΠ (λ ↑v → QCEval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩)

        [_]* : (s : Shape) → (v : Pos s → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩
        [ s ]* = QCEval.Label→⟦ Q ⟧ᵗ

        [_]*-loop : ∀ s → (σ : Symm s) → PathP (λ i → (ua (σ .fst) i → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩) [ s ]* [ s ]*
        [_]*-loop s σ = funExtDep λ { {x₀ = v} {x₁ = w} p → ⟦Q⟧.LabelEquiv→⟦_⟧Path v w $ ∃-intro σ p }

        goal : (s : ↑Shape) → (v : ↑Pos s → ⟨ X ⟩) → ⟦Q⟧ᵗ ⟨ X ⟩
        goal = ↑Q.↑Shape-uncurry λ s → ↑SymmElim.elimSet s (λ σ → isSetΠ⟦Q⟧ ↑⟨ s , σ ⟩) [ s ]* [ s ]*-loop

    opaque
      unfolding from-lift
      from-lift-trunc : ⟨ Tr ⟦↑Q⟧ X ⟩ → (⟦Q⟧ᵗ ⟨ X ⟩)
      from-lift-trunc = ST.rec (QCEval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩) from-lift

    opaque
      unfolding ⟦↑Q⟧ from-lift-trunc to-lift-trunc
      lift-trunc-rightInv : ∀ (x : ⟨ Tr ⟦↑Q⟧ X ⟩) → to-lift-trunc (from-lift-trunc x) ≡ x
      lift-trunc-rightInv = ST.elim (isProp→isSet ∘ isPropPath) goal where
        isPropPath : ∀ x → isProp (to-lift-trunc (from-lift-trunc x) ≡ x)
        isPropPath x = ST.isSetSetTrunc _ x

        workhorse : (s : Shape) (v : Pos s → ⟨ X ⟩) → to-lift-trunc (from-lift-trunc ST.∣ ↑Q.↑shape s , v ∣₂) ≡ ST.∣ ↑Q.↑shape s , v ∣₂
        workhorse s v = refl

        lemma : ∀ (s : ↑Shape) (v : ↑Pos s → ⟨ X ⟩) → to-lift-trunc (from-lift-trunc ST.∣ (s , v) ∣₂) ≡ ST.∣ (s , v) ∣₂
        lemma = ↑Q.↑Shape-uncurry λ s → ↑SymmElim.elimProp s (λ σ → isPropΠ λ v → isPropPath ST.∣ ↑⟨ s , σ ⟩ , v ∣₂) (workhorse s)

        goal : ∀ (x : ⟦↑Q⟧ᵗ ⟨ X ⟩) → to-lift-trunc (from-lift-trunc ST.∣ x ∣₂) ≡ ST.∣ x ∣₂
        goal = uncurry lemma

    opaque
      unfolding from-lift-trunc to-lift-trunc
      lift-trunc-leftInv : ∀ (x : ⟦Q⟧ᵗ ⟨ X ⟩) → (from-lift-trunc (to-lift-trunc x)) ≡ x
      lift-trunc-leftInv = QCEval.⟦ Q ⟧ᵗ-elimProp {P = Motive} isPropMotive {! !} where
      -- lift-trunc-leftInv QCEval.mk⟦ s , v ⟧ᵗ = SQ.elimProp {P = Motive} isPropMotive [_]* v where
        Motive : ⟦Q⟧ᵗ ⟨ X ⟩ → Type ℓ
        Motive x = from-lift-trunc (to-lift-trunc x) ≡ x

        isPropMotive : ∀ x → isProp (Motive x)
        isPropMotive x = QCEval.isSet-⟦ Q ⟧ᵗ ⟨ X ⟩ _ _

        -- [_]* : ∀ {s} → (v : Pos s → ⟨ X ⟩) → Motive ?
        -- [ v ]* = refl

    lift-trunc-Iso : Iso (⟦Q⟧ᵗ ⟨ X ⟩) ⟨ Tr ⟦↑Q⟧ X ⟩
    lift-trunc-Iso .Iso.fun = to-lift-trunc
    lift-trunc-Iso .Iso.inv = from-lift-trunc
    lift-trunc-Iso .Iso.rightInv = lift-trunc-rightInv
    lift-trunc-Iso .Iso.leftInv = lift-trunc-leftInv

  opaque
    unfolding CoffinEval.⟦_⟧
    evalLiftEquiv : ∀ X → ⟨ ⟦Q⟧ X ⟩ ≃ ⟨ Tr ⟦↑Q⟧ X ⟩
    evalLiftEquiv X =
      ⟦Q⟧ᵗ ⟨ X ⟩ ≃⟨ Isomorphism.isoToEquiv (LiftTruncEquiv.lift-trunc-Iso X) ⟩
      ∥ CoffinEval.⟦ ↑Q ⟧ᵗ ⟨ X ⟩ ∥₂ ≃∎

  evalLiftPath : ∀ X → ⟦Q⟧ X ≡ Tr ⟦↑Q⟧ X
  evalLiftPath X = TypeOfHLevel≡ 2 (ua $ evalLiftEquiv X)

module EvalLiftLoopEquational {ℓ} (Q : QCont ℓ) where
  open module Q = QCont Q using (Shape ; Pos ; Symm ; PosSet)
  open module ⟦Q⟧ = QCEval Q using (_∼*_) renaming (⟦_⟧ to ⟦Q⟧ ; ⟦_⟧ᵗ to ⟦Q⟧ᵗ)

  open module ↑Q = Lift Q using (↑Shape ; ↑Pos ; ↑⟨_,_⟩ ; ↑Symm ; module ↑SymmElim) renaming (↑ to ↑Q)
  open module ⟦↑Q⟧ = CoffinEval ↑Q using () renaming (⟦_⟧ to ⟦↑Q⟧ ; ⟦_⟧ᵗ to ⟦↑Q⟧ᵗ ; ⟦-⟧ᵗ-Path to ⟦↑Q⟧ᵗ-Path)

  module PosEquiv (X : Type ℓ) (s : Shape) where
    private
      ∥ΣPos→X∥₂ = ∥ Σ[ σ ∈ ↑Symm s ] (↑Pos ↑⟨ s , σ ⟩ → X) ∥₂
      Pos→X/∼ = (Pos s → X) / _∼*_

    opaque
      unfolding Q.PosPath
      PosIso : Iso ∥ΣPos→X∥₂ Pos→X/∼
      PosIso = record { the-iso } where module the-iso where
        fun : ∥ΣPos→X∥₂ → Pos→X/∼
        fun = ST.rec SQ.squash/ $ uncurry
          $ ↑SymmElim.elimSet s
            (λ σ → isSetΠ λ v → SQ.squash/)
            SQ.[_]
            (λ σ → funExtDep λ {x₀ = v} {x₁ = w} vσ≡w → SQ.eq/ v w $ ∃-intro σ vσ≡w)

        inv : Pos→X/∼ → ∥ΣPos→X∥₂
        inv = SQ.rec ST.isSetSetTrunc
          (λ v → ST.∣ ↑Symm.⋆ , v ∣₂)
          λ v w → ∃-rec (ST.isSetSetTrunc _ _) λ σ label-path → cong ST.∣_∣₂ $ ΣPathP $ ↑Symm.loop σ , label-path

        leftInv : _
        leftInv = ST.elim (λ ∣v∣ → isProp→isSet (ST.isSetSetTrunc _ ∣v∣))
          $ uncurry (↑SymmElim.elimProp s (λ (σ : ↑Symm s) → isPropΠ λ v → ST.isSetSetTrunc _ ST.∣ σ , v ∣₂) λ _ → refl)

        rightInv : _
        rightInv = SQ.elimProp (λ v/∼ → SQ.squash/ _ v/∼) λ _ → refl

    PosEquiv :  ∥ Σ[ σ ∈ ↑Symm s ] (↑Pos ↑⟨ s , σ ⟩ → X) ∥₂ ≃ ((Pos s → X) / _∼*_)
    PosEquiv = isoToEquiv PosIso

  opaque
    unfolding ⟦↑Q⟧
    thm : ∀ X → ⟨ Tr ⟦↑Q⟧ X ⟩ ≃ ⟨ ⟦Q⟧ X ⟩
    thm X =
      ∥ ⟦↑Q⟧ᵗ ⟨ X ⟩ ∥₂ ≃⟨⟩
      ∥ Σ[ ↑s ∈ ↑Shape ] (↑Pos (↑s) → ⟨ X ⟩) ∥₂                       ≃⟨ cong≃ ∥_∥₂ Sigma.Σ-assoc-≃ ⟩
      ∥ Σ[ s ∈ Shape ] Σ[ v ∈ ↑Symm s ] (↑Pos ↑⟨ s , v ⟩ → ⟨ X ⟩) ∥₂  ≃⟨ setTruncateFstΣ≃ Q.is-set-shape ⟩
      Σ[ s ∈ Shape ] ∥ Σ[ v ∈ ↑Symm s ] (↑Pos ↑⟨ s , v ⟩ → ⟨ X ⟩) ∥₂  ≃⟨ Sigma.Σ-cong-equiv-snd $ PosEquiv.PosEquiv ⟨ X ⟩ ⟩
      Σ[ s ∈ Shape ] (Pos s → ⟨ X ⟩) / _∼*_                           ≃⟨ (⟦Q⟧ᵗ ⟨ X ⟩ ≃Σ) ⁻ᵉ ⟩
      ⟨ ⟦Q⟧ X ⟩                                                       ≃∎

private module ViaGAction where
  open import Cubical.Algebra.Group
  open import Cubical.Algebra.Group.Morphisms

  Aut : ∀ {ℓ} (X : hSet ℓ) → Group (ℓ-suc ℓ)
  Aut X = makeGroup {G = ⟨ X ⟩ ≡ ⟨ X ⟩}
    refl
    _∙_
    sym
    (isOfHLevel≡ 2 (str X) (str X))
    {!assoc !} {! !} {! !} {! !} {! !}

  module _ {ℓ} (G : Group ℓ) (X : hSet ℓ) (η : GroupHom G (Aut X)) where
    open import GpdCont.Delooping ⟨ G ⟩ (str G) as BG' renaming (𝔹 to BG)
    open import Cubical.HITs.GroupoidQuotients as GQ using (_//_)

    𝕏 : BG → hSet ℓ
    𝕏 = BG'.rec isGroupoidHSet X
      (λ g → TypeOfHLevel≡ 2 (η .fst g))
      λ where
        g h i j .fst → {! η .snd !}
        g h i j .snd → {! !}

    -- Total space of the associated bundle (Symmetry 4.7.13)
    ∫𝕏 : Type _
    ∫𝕏 = Σ[ g ∈ BG ] ⟨ 𝕏 g ⟩

    -- x ∼ y ⇔ ∃[ g ] x ≡ transport (η g) y
    _∼_ : (x y : ⟨ X ⟩) → Type _
    x ∼ y = ∃[ g ∈ ⟨ G ⟩ ] PathP (λ i → η .fst g i) x y

    orbit-comp : {! !}
    orbit-comp = {! !}

    Orbit : Type _
    Orbit = ⟨ X ⟩ / _∼_

    fwd : ∥ ∫𝕏 ∥₂ → Orbit
    fwd = ST.rec SQ.squash/ (uncurry fwd') where
      fwd-loop : (g : ⟨ G ⟩) → PathP (λ i → η .fst g i → Orbit) SQ.[_] SQ.[_]
      fwd-loop g = funExtDep λ {x₀} {x₁} (x₀≡x₁ : PathP (λ i → η .fst g i) x₀ x₁) → SQ.eq/ x₀ x₁ PT.∣ g , x₀≡x₁ ∣₁

      fwd' : (g : BG) (x : ⟨ 𝕏 g ⟩) → Orbit
      fwd' = BG'.elimSet (λ g → isSetΠ λ x → SQ.squash/) SQ.[_] fwd-loop

    bwd : Orbit → ∥ ∫𝕏 ∥₂
    bwd = SQ.rec ST.isSetSetTrunc ∫ well-defined where
      ∫ : ⟨ X ⟩ → ∥ ∫𝕏 ∥₂
      ∫ x = ST.∣ BG.⋆ , x ∣₂

      well-defined : (x y : ⟨ X ⟩) → x ∼ y → ∫ x ≡ ∫ y
      well-defined x y = PT.rec (ST.isSetSetTrunc _ _) $ uncurry well-defined' where
        well-defined' : (g : ⟨ G ⟩) (p : PathP (λ i → η .fst g i) x y) → ∫ x ≡ ∫ y
        well-defined' g p = cong ST.∣_∣₂ (ΣPathP (BG.loop g , p))

    ost-iso : Iso ∥ ∫𝕏 ∥₂ Orbit
    ost-iso .Iso.fun = fwd
    ost-iso .Iso.inv = bwd
    ost-iso .Iso.rightInv = SQ.elimProp (λ _ → SQ.squash/ _ _) λ _ → refl
    ost-iso .Iso.leftInv = ST.elim (λ _ → isProp→isSet $ ST.isSetSetTrunc _ _)
      $ uncurry
      $ BG'.elimProp {B = λ g → (x : ⟨ 𝕏 g ⟩) → bwd (fwd ST.∣ g , x ∣₂) ≡ ST.∣ g , x ∣₂}
        (λ g → isPropΠ λ x → ST.isSetSetTrunc _ _)
        λ x → refl {x = ST.∣ BG.⋆ , x ∣₂}

    ost : ∥ ∫𝕏 ∥₂ ≃ Orbit
    ost = isoToEquiv ost-iso
