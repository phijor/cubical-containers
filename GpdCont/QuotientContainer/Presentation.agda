module GpdCont.QuotientContainer.Presentation where

open import GpdCont.Prelude
open import GpdCont.QuotientContainer.Base
open import GpdCont.QuotientContainer.Morphism as QMor using (QContMorphism)
open import GpdCont.QuotientContainer.Category using (Eval)
import GpdCont.QuotientContainer.Eval as QEval

import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua→⁻)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.HITs.SetQuotients as SQ

open import Cubical.Data.Equality as Eq using () renaming (_≡_ to Eq ; refl to reflEq)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor hiding (Id)
open import Cubical.Categories.Functors.Constant using (Constant)
open import Cubical.Categories.Functor.Compose using (precomposeF)
open import Cubical.Categories.NaturalTransformation.Base as NT using (NatTrans ; NatIso)
open import Cubical.Categories.Adjoint using (module UnitCounit ; module NaturalBijection) renaming (adj→adj' to UnitCounit→NaturalBijection)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors using (FUNCTOR)
open import Cubical.Categories.Presheaf.KanExtension as KanExt using (module Lan)

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
    the-iso .Iso.rightInv (reflEq , σ) = refl
    the-iso .Iso.leftInv (symm σ) = refl

  Shape[-,-]Iso : ∀ {s t} → Iso Shape[ s , t ] ((s ≡ t) × Symm s)
  Shape[-,-]Iso {s} {t} =
    Shape[ s , t ] Iso⟨ Shape[-,-]EqIso ⟩
    Eq s t × Symm s Iso⟨ Σ-cong-iso-fst $ invIso Eq.PathIsoEq ⟩
    (s ≡ t) × Symm s ∎Iso

  opaque
    𝕊 : Category ℓ ℓ
    𝕊 .Category.ob = Shape
    𝕊 .Category.Hom[_,_] = Shape[_,_]
    𝕊 .Category.id = symm $ SymmGroup.1g _
    𝕊 .Category._⋆_ (symm σ) (symm τ) = symm (τ · σ)
    𝕊 .Category.⋆IdL (symm σ) = cong symm $ SymmGroup.·IdR _ σ
    𝕊 .Category.⋆IdR (symm σ) = cong symm $ SymmGroup.·IdL _ σ
    𝕊 .Category.⋆Assoc (symm σ) (symm τ) (symm υ) = cong symm $ SymmGroup.·Assoc _ υ τ σ
    𝕊 .Category.isSetHom = isOfHLevelRetractFromIso 2 Shape[-,-]Iso $
      isSet× (isProp→isSet $ (is-set-shape _ _)) isSetSymm

    ⌜_⌝ : Functor 𝕊 (SET ℓ ^op)
    ⌜_⌝ .Functor.F-ob = PosSet
    ⌜_⌝ .Functor.F-hom (symm σ) = σ ⁺
    ⌜_⌝ .Functor.F-id = refl
    ⌜_⌝ .Functor.F-seq (symm σ) (symm τ) = refl

  module Extension = Lan ℓ {C = 𝕊} {D = SET ℓ ^op} ⌜_⌝

  Extension : Functor (SET ℓ) (SET ℓ)
  Extension = Extension.LanOb K₁

  ExtensionRaw : (X : hSet ℓ) → Type ℓ
  ExtensionRaw = Extension.Raw K₁
  
  -- Sanity check:
  opaque
    unfolding 𝕊
    _ : ∀ X → ExtensionRaw X ≡ (Σ[ s ∈ Shape ] (Pos s → ⟨ X ⟩) × Unit* {ℓ = ℓ})
    _ = λ _ → refl

  ⟨_⟩[_≈_] : (X : hSet ℓ) → (x y : ExtensionRaw X) → Type ℓ
  ⟨_⟩[_≈_] = Extension._≈_ K₁

  opaque
    unfolding QEval.⟦_⟧ 𝕊
    α⁺-ob : (X : hSet ℓ) → ⟨ Extension ⟅ X ⟆ ⟩ → ⟨ Eval Q ⟅ X ⟆ ⟩
    α⁺-ob X = SQ.rec (str $ Eval Q ⟅ X ⟆) raw pres≈ where
      raw : ExtensionRaw X → ⟨ Eval Q ⟅ X ⟆ ⟩
      raw = map-snd λ { (label , _) → SQ.[ label ] }

      pres≈ : ∀ x y → ⟨ X ⟩[ x ≈ y ] → raw x ≡ raw y
      pres≈ x ._ (Lan.shift {c = s} {c' = t} label (symm σ) _) = QEval.preComp→⟦ Q ⟧Path {X = X} label σ

    α⁻-ob : (X : hSet ℓ) → ⟨ Eval Q ⟅ X ⟆ ⟩ → ⟨ Extension ⟅ X ⟆ ⟩
    α⁻-ob X = uncurry λ s → SQ.rec (str $ Extension ⟅ X ⟆) raw pres∼* where module _ {s : Shape} where
      raw : (Pos s → ⟨ X ⟩) → ⟨ Extension ⟅ X ⟆ ⟩
      raw label = SQ.[ s , label , tt* ]

      pres∼* : ∀ x y → QEval._∼*_ Q x y → raw x ≡ raw y
      pres∼* x y (σ , r) = SQ.eq/ _ _ (subst (λ f → ⟨ X ⟩[ s , f , tt* ≈ s , y , tt* ]) x-decomp (Lan.shift y (symm σ) tt*)) where
        x-decomp : σ Q.◁ y ≡ x
        x-decomp = funExt $ sym ∘ ua→⁻ r

    α-sec : (X : hSet ℓ) → (α⁺-ob X) ∘ (α⁻-ob X) ≡ id ⟨ Eval Q ⟅ X ⟆ ⟩
    α-sec X = funExt $ uncurry λ s → SQ.elimProp (λ x → str (Eval Q ⟅ X ⟆) _ _) λ _ → refl

    α-ret : (X : hSet ℓ) → (α⁻-ob X) ∘ (α⁺-ob X) ≡ id ⟨ Extension ⟅ X ⟆ ⟩
    α-ret X = funExt $ SQ.elimProp (λ x → str (Extension ⟅ X ⟆) _ _) λ x → refl

  opaque
    unfolding α⁺-ob QEval.⟦_⟧-map 𝕊
    α-hom-ext : ∀ {X Y : hSet ℓ} (f : SET _ [ X , Y ]) → ∀ x → α⁺-ob Y (Extension ⟪ f ⟫ $ x) ≡ (Eval Q ⟪ f ⟫ $ (α⁺-ob X x))
    α-hom-ext {X} {Y} f = SQ.elimProp (λ x → str (Eval Q ⟅ Y ⟆) _ _)
      λ { (s , label , tt*) → refl }

  α : NatTrans Extension (Eval Q)
  α .NatTrans.N-ob = α⁺-ob
  α .NatTrans.N-hom f = funExt $ α-hom-ext f

  -- Lemma 3.6 in [AAGMcB]
  thm : NatIso Extension (Eval Q)
  thm .NatIso.trans = α
  thm .NatIso.nIso X .isIso.inv = α⁻-ob X
  thm .NatIso.nIso X .isIso.sec = α-sec X
  thm .NatIso.nIso X .isIso.ret = α-ret X

  -- TODO: Type checks, but is slow.
  -- opaque
  --   ExtensionFunctor : Functor (FUNCTOR (𝕊 ^op) (SET ℓ)) (FUNCTOR (SET ℓ ^op ^op) (SET ℓ))
  --   ExtensionFunctor = Extension.Lan

  -- opaque
  --   UP : Extension.Lan UnitCounit.⊣ (precomposeF {C = 𝕊 ^op} {D = (SET ℓ ^op) ^op} (SET ℓ) (⌜_⌝ ^opF))
  --   UP = Extension.adj

  --   UP' : Extension.Lan NaturalBijection.⊣ (precomposeF {C = 𝕊 ^op} {D = (SET ℓ ^op) ^op} (SET ℓ) (⌜_⌝ ^opF))
  --   UP' = UnitCounit→NaturalBijection Extension.Lan (precomposeF (SET ℓ) (⌜_⌝ ^opF)) UP

  -- UP-Iso : Iso (NatTrans Extension Extension) (NatTrans K₁ (Extension ∘F (⌜_⌝ ^opF)))
  -- UP-Iso = NaturalBijection._⊣_.adjIso UP'

module MorphismCorrespondence {ℓ} (Q R : QCont ℓ) where
  opaque
    unfolding 𝕊 ⌜_⌝
    lemma42 : Iso (QContMorphism Q R) (NatTrans (K₁ ^opF) ((Extension R ^opF) ∘F ⌜ Q ⌝))
    lemma42 =
      QContMorphism Q R Iso⟨ _ IsoΣ ⟩
      QContMorphism Q R asΣ Iso⟨ {! !} ⟩
      (NatTrans (K₁ ^opF) ((Extension R ^opF) ∘F ⌜ Q ⌝)) ∎Iso

  -- thm43 : Iso (QContMorphism Q R) (NatTrans (Eval Q) (Eval R))
  -- thm43 = {! !}

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
