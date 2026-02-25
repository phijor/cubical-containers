{-# OPTIONS --lossy-unification #-}
module GpdCont.QuotientContainer.Presentation where

open import GpdCont.Prelude
open import GpdCont.QuotientContainer.Base
open import GpdCont.QuotientContainer.Premorphism as PMor
open import GpdCont.QuotientContainer.Morphism as QMor
open import GpdCont.QuotientContainer.Category using (Eval ; QCONT)
import GpdCont.QuotientContainer.Eval as QEval

open import GpdCont.KanExtension.Left

import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua→⁻ ; ua)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Functions.FunExtEquiv
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Equality as Eq using () renaming (_≡_ to Eq ; refl to reflEq)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor hiding (Id)
open import Cubical.Categories.Functors.Constant using (Constant)
open import Cubical.Categories.Functor.Compose using (precomposeF)
open import Cubical.Categories.NaturalTransformation as NT using (NatTrans ; NatIso ; _∘ˡ_) renaming (_●ᵛ_ to _∙ᵛ_)
open import Cubical.Categories.Adjoint using (module UnitCounit ; module NaturalBijection) renaming (adj→adj' to UnitCounit→NaturalBijection)
open import Cubical.Categories.Instances.Sets as SetCat using (SET)
open import Cubical.Categories.Instances.Functors using (FUNCTOR)

private
  K₁ : ∀ {ℓo ℓh ℓ} {C : Category ℓo ℓh} → Functor C (SET ℓ)
  K₁ = Constant _ _ (Unit* , isSetUnit*)

module _ {ℓ} (Q : QCont ℓ) where
  open module Q = QCont Q

  data Shape[_,_] (s : Shape) : Shape → Type ℓ where
    symm : (σ : Symm s) → Shape[ s , s ]

  Shape[-,-]EqIso : ∀ {s t} → Iso Shape[ s , t ] (Eq s t × Symm s)
  Shape[-,-]EqIso {s} {t} = the-iso where
    the-iso : Iso _ _
    the-iso .Iso.fun (symm σ) = reflEq , σ
    the-iso .Iso.inv (reflEq , σ) = symm σ
    the-iso .Iso.sec (reflEq , σ) = refl
    the-iso .Iso.ret (symm σ) = refl

  Shape[-,-]Iso : ∀ {s t} → Iso Shape[ s , t ] ((s ≡ t) × Symm s)
  Shape[-,-]Iso {s} {t} =
    Shape[ s , t ] Iso⟨ Shape[-,-]EqIso ⟩
    Eq s t × Symm s Iso⟨ Σ-cong-iso-fst $ invIso Eq.PathIsoEq ⟩
    (s ≡ t) × Symm s ∎Iso

  𝕊 : Category ℓ ℓ
  𝕊 .Category.ob = Shape
  𝕊 .Category.Hom[_,_] = Shape[_,_]
  𝕊 .Category.id = symm $ SymmGroup.1g _
  𝕊 .Category._⋆_ (symm σ) (symm τ) = symm (σ · τ)
  𝕊 .Category.⋆IdL (symm σ) = cong symm $ SymmGroup.·IdL _ σ
  𝕊 .Category.⋆IdR (symm σ) = cong symm $ SymmGroup.·IdR _ σ
  𝕊 .Category.⋆Assoc (symm σ) (symm τ) (symm υ) = sym $ cong symm $ SymmGroup.·Assoc _ σ τ υ
  𝕊 .Category.isSetHom = isOfHLevelRetractFromIso 2 Shape[-,-]Iso $
    isSet× (isProp→isSet $ (is-set-shape _ _)) isSetSymm

  ⌜_⌝ : Functor 𝕊 (SET ℓ)
  ⌜_⌝ .Functor.F-ob = PosSet
  ⌜_⌝ .Functor.F-hom (symm σ) = σ ⁺
  ⌜_⌝ .Functor.F-id = refl
  ⌜_⌝ .Functor.F-seq (symm σ) (symm τ) = refl

  module Extension = Lan {C = 𝕊} ⌜_⌝

  module EvalFiller where
    ob : (s : Shape) → QEval.⟦ Q ⟧ᵗ (Pos s)
    ob s = QEval.Label→⟦ Q ⟧ᵗ (id (Pos s))

    hom : (s : Shape) (σ : Symm s) → Path (QEval.⟦ Q ⟧ᵗ (Pos s)) (ob s) (QEval.Label→⟦ Q ⟧ᵗ (σ ⁺))
    hom s σ = sym $ QEval.preComp→⟦ Q ⟧Path {X = PosSet s} (id _) σ

  EvalFiller : NatTrans K₁ (Eval Q ∘F ⌜_⌝)
  EvalFiller .NatTrans.N-ob s tt* = EvalFiller.ob s
  EvalFiller .NatTrans.N-hom {x = s} (symm σ) = funExt λ { tt* → EvalFiller.hom s σ }

    -- EvalFillerIso : NatIso K₁ (Eval Q ∘F ⌜_⌝)
    -- EvalFillerIso .NatIso.trans = EvalFiller
    -- EvalFillerIso .NatIso.nIso s = SetCat.Iso→CatIso nat-iso .snd where
    --   nat-iso : Iso (Unit* {ℓ}) ⟨ Eval Q ⟅ PosSet s ⟆ ⟩
    --   nat-iso .Iso.fun = λ _ → EvalFiller.ob s
    --   nat-iso .Iso.inv = λ _ → tt*
    --   nat-iso .Iso.sec = QEval.⟦ Q ⟧ᵗ-elimProp (λ x → (str $ Eval Q ⟅ PosSet s ⟆) _ _) λ {t} label → {! !}
    --   nat-iso .Iso.ret tt* = refl

  LanExtension : Extension.Extension {D = SET ℓ} K₁
  LanExtension .Lan.Extension.ext = Eval Q
  LanExtension .Lan.Extension.ext-filler = EvalFiller

  module _ (e : Extension.Extension {D = SET ℓ} K₁) where
    open Lan.Extension e renaming (ext to F ; ext-filler to α)

    open QEval using (⟦_⟧ᵗ-rec)

    _ : Functor (SET ℓ) (SET ℓ)
    _ = F

    _ : NatTrans K₁ (F ∘F ⌜_⌝)
    _ = α

    private
      α′ : (s : Shape) → ⟨ F ⟅ PosSet s ⟆ ⟩
      α′ s = α NT.⟦ s ⟧ $ tt*

      opaque
        α-nat : ∀ {s : Shape} (σ : Symm s) → α′ s ≡ (F ⟪ σ ⁺ ⟫ $ α′ s)
        α-nat {s} σ = funExt⁻ (α .NatTrans.N-hom (symm σ)) tt*

      α*-ob-rep : ∀ X {s} → (label : Pos s → ⟨ X ⟩) → ⟨ F ⟅ X ⟆ ⟩
      α*-ob-rep _ {s} label = F ⟪ label ⟫ $ α′ s

      opaque
        α*-ob-rep-well-defined : ∀ X {s} → (l₀ l₁ : Pos s → ⟨ X ⟩) → QEval.LabelEquiv Q s ⟨ X ⟩ l₀ l₁ → α*-ob-rep X l₀ ≡ α*-ob-rep X l₁
        α*-ob-rep-well-defined X {s} l₀ l₁ = PT.rec (str (F ⟅ X ⟆) _ _) λ (σ , pσ) →
          (F ⟪ l₀ ⟫ $ α′ s)
            ≡⟨ cong (λ · → F ⟪ · ⟫ $ α′ s) (funExt $ ua→⁻ pσ) ⟩
          (F ⟪ l₁ ∘ σ ⁺ ⟫ $ α′ s)
            ≡⟨ cong (_$ α′ s) (Functor.F-seq F (σ ⁺) l₁) ⟩
          (F ⟪ l₁ ⟫ $ F ⟪ σ ⁺ ⟫ $ α′ s)
            ≡⟨ cong (F ⟪ l₁ ⟫) $ sym $ α-nat σ ⟩
          (F ⟪ l₁ ⟫ $ α′ s)
            ∎

      α*-ob : (X : hSet ℓ) → ⟨ Eval Q ⟅ X ⟆ ⟩ → ⟨ F ⟅ X ⟆ ⟩
      α*-ob X = ⟦ Q ⟧ᵗ-rec (str $ F ⟅ X ⟆) (α*-ob-rep X) (α*-ob-rep-well-defined X)

      opaque
        α*-ob-factorization : ∀ s → α′ s ≡ α*-ob _ (EvalFiller.ob s)
        α*-ob-factorization s =
          α′ s ≡⟨ cong (_$ α′ s) $ sym $ Functor.F-id F ⟩
          (F ⟪ id _ ⟫ $ α′ s) ≡⟨⟩
          α*-ob (PosSet s) (QEval.Label→⟦ Q ⟧ᵗ (id (Pos s))) ∎

    private opaque
      α*-hom : ∀ {X Y} → (f : SET ℓ [ X , Y ]) → QEval.⟦ Q ⟧-map {X} {Y} f ⋆ α*-ob Y ≡ α*-ob X ⋆ F ⟪ f ⟫
      α*-hom {X} {Y} f = funExt $ QEval.⟦ Q ⟧ᵗ-elimProp {P = λ _ → Path ⟨ F ⟅ Y ⟆ ⟩ _ _}
        (λ _ → isOfHLevelPath' 1 (str $ F ⟅ Y ⟆) _ _)
        goal where
        F⟪f⟫ : SET ℓ [ F ⟅ X ⟆ , F ⟅ Y ⟆ ]
        F⟪f⟫ = F ⟪ f ⟫

        goal : ∀ {s} → (label : Pos s → ⟨ X ⟩) → (F ⟪ f ∘ label ⟫ $ α′ s) ≡ (F⟪f⟫ ∘ F ⟪ label ⟫ $ α′ s)
        goal {s} label = cong (_$ α′ s) (Functor.F-seq F label f)

    α* : NatTrans (Eval Q) F
    α* .NatTrans.N-ob = α*-ob
    α* .NatTrans.N-hom = α*-hom

    opaque
      α*-factorization : α ≡ EvalFiller ∙ᵛ (α* ∘ˡ ⌜_⌝)
      α*-factorization = NT.makeNatTransPath $ funExt₂ λ { s tt* → α*-ob-factorization s }

    module _ (β* : NatTrans (Eval Q) F) (β*-factorization : α ≡ EvalFiller ∙ᵛ (β* ∘ˡ ⌜_⌝)) where
      opaque
        foo : ∀ s → α′ s ≡ (β* NT.⟦ PosSet s ⟧) (EvalFiller.ob s)
        foo s = funExt⁻ ((funExt⁻ $ cong NatTrans.N-ob β*-factorization) s) tt*

        β*-nat-label : ∀ X {s} (label : Pos s → ⟨ X ⟩) → (F ⟪ label ⟫ ∘ β* NT.⟦ PosSet s ⟧) ≡ (β* NT.⟦ X ⟧ ∘ QEval.⟦ Q ⟧-map {PosSet s} {X} label)
        β*-nat-label X label = sym $ β* .NatTrans.N-hom label

        lemma : ∀ X {s} (label : Pos s → ⟨ X ⟩) → QEval.⟦ Q ⟧-map {PosSet s} {X} label (EvalFiller.ob s) ≡ (QEval.Label→⟦ Q ⟧ᵗ label)
        lemma X {s} label = refl

        α*-unique-ext : ∀ X {s} (label : Pos s → ⟨ X ⟩) → (F ⟪ label ⟫) (α′ s) ≡ (β* NT.⟦ X ⟧) (QEval.Label→⟦ Q ⟧ᵗ label)
        α*-unique-ext X {s} label =
          (F ⟪ label ⟫) (α′ s)
            ≡⟨ cong (F ⟪ label ⟫) (foo s) ⟩
          (F ⟪ label ⟫ $ β* NT.⟦ PosSet s ⟧ $ EvalFiller.ob s)
            ≡⟨ funExt⁻ (β*-nat-label X label) $ EvalFiller.ob s ⟩
          (β* NT.⟦ X ⟧ $ QEval.⟦ Q ⟧-map {PosSet s} {X} label $ EvalFiller.ob s)
            ≡⟨ cong (β* NT.⟦ X ⟧) (lemma X label) ⟩
          (β* NT.⟦ X ⟧) (QEval.Label→⟦ Q ⟧ᵗ label)
            ∎

        α*-unique-ob : ∀ X → α* NT.⟦ X ⟧ ≡ β* NT.⟦ X ⟧
        α*-unique-ob X = funExt $ QEval.⟦ Q ⟧ᵗ-elimProp (λ x → str (F ⟅ X ⟆) _ _) (α*-unique-ext X)

        α*-unique : α* ≡ β*
        α*-unique = NT.makeNatTransPath $ funExt α*-unique-ob

    isLanLanExtension : ∃![ α* ∈ NatTrans (Eval Q) F ] α ≡ EvalFiller ∙ᵛ (α* ∘ˡ ⌜_⌝)
    isLanLanExtension .fst = α* , α*-factorization
    isLanLanExtension .snd (β* , β*-factorization) = Σ≡Prop (λ β* → NT.isSetNatTrans _ _) (α*-unique β* β*-factorization)

  Lan : Lan.Lan ⌜_⌝ K₁
  Lan .Lan.Lan.extension = LanExtension
  Lan .Lan.Lan.is-lan-extension = isLanLanExtension

{-
module MorphismCorrespondence {ℓ} (Q R : QCont ℓ) where
  opaque
    unfolding 𝕊 ⌜_⌝
    lemma42 : Iso (QCONT _ [ Q , R ]) (NatTrans (K₁ ^opF) ((Extension R ^opF) ∘F ⌜ Q ⌝))
    lemma42 =
      QCONT _ [ Q , R ] Iso⟨ _ IsoΣ ⟩
      QCONT _ [ Q , R ] asΣ Iso⟨ {! !} ⟩
      (NatTrans (K₁ ^opF) ((Extension R ^opF) ∘F ⌜ Q ⌝)) ∎Iso

  open QCont

  opaque
    unfolding 𝕊 ⌜_⌝
    thm43 : Iso (QCONT _ [ Q , R ]) (NatTrans (Eval Q) (Eval R))
    thm43 =
      QCONT _ [ Q , R ] Iso⟨ lemma42 ⟩
      (NatTrans (K₁ ^opF) ((Extension R ^opF) ∘F ⌜ Q ⌝)) Iso⟨ _ IsoΣ ⟩
      Σ[ ob ∈ ((q : Shape Q) → _ → Unit*) ]
        NT.N-hom-Type (K₁ ^opF) ((Extension R ^opF) ∘F ⌜ Q ⌝) ob Iso⟨ Σ-contractFstIso (isContrΠ λ q → isContrΠ λ _ → isContrUnit*) ⟩
      NT.N-hom-Type (K₁ ^opF) ((Extension R ^opF) ∘F ⌜ Q ⌝) (λ _ _ → tt*) Iso⟨ idIso ⟩
      ({q q′ : Shape Q} (f : 𝕊 Q [ q , q′ ]) → (λ _ → tt*) ≡ (λ _ → tt*)) Iso⟨ {! !} ⟩
      (NatTrans (Eval Q) (Eval R)) asΣ Iso⟨ invIso $ _ IsoΣ ⟩
      (NatTrans (Eval Q) (Eval R)) ∎Iso
-}

{-
private module Example where
  open import Cubical.Data.Bool
  open import Cubical.Data.Sum

  open QCont

  UPair : QCont ℓ-zero
  UPair .Shape = Unit
  UPair .Pos _ = Bool
  UPair .isSymm σ = Unit
  UPair .is-set-shape = isSetUnit
  UPair .is-set-pos _ = isSetBool
  UPair .is-prop-symm _ = isPropUnit
  UPair .symm-id _ = tt
  UPair .symm-sym _ _ = tt
  UPair .symm-comp _ _ _ _ = tt

  swap : 𝕊 UPair [ tt , tt ]
  swap = symm (notEquiv , tt)

  _ :  ⌜ UPair ⌝ ⟪ swap ⟫ ≡ not
  _ = refl
  -}
