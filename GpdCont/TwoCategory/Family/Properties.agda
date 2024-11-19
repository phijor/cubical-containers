{-# OPTIONS --lossy-unification #-}
module GpdCont.TwoCategory.Family.Properties where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.LocalCategory
open import GpdCont.TwoCategory.LocalFunctor
open import GpdCont.TwoCategory.Family.Base
open import GpdCont.TwoCategory.Family.Functor
open import GpdCont.TwoCategory.Displayed.Base
open import GpdCont.Axioms.TruncatedChoice using (ASC)

open import Cubical.Foundations.Equiv as Equiv using (isEquiv)
open import Cubical.Foundations.HLevels using (isSetΣ ; hSet)
import      Cubical.Data.Sigma as Sigma
import      Cubical.Data.Equality as Eq
import      Cubical.HITs.PropositionalTruncation as PT
import      Cubical.Categories.Category.Base as Category

module _
  {ℓo ℓh ℓr ℓo′ ℓh′ ℓr′}
  {C : TwoCategory ℓo ℓh ℓr}
  {D : TwoCategory ℓo′ ℓh′ ℓr′}
  (F : LaxFunctor C D)
  (ℓ : Level)
  where
  private
    module C = TwoCategory C
    module D = TwoCategory D
    module FamC = TwoCategory (Fam C ℓ)
    module FamD = TwoCategory (Fam D ℓ)
    module F = LaxFunctor F
    module LiftF = LaxFunctor (LiftFunctor F ℓ)

  isLocallyFullyFaithfulFam : isLocallyFullyFaithful F → isLocallyFullyFaithful (LiftFunctor F ℓ)
  isLocallyFullyFaithfulFam is-locally-ff-F x y f g = goal where
    FamF₂-equiv : FamC.rel {x} {y} f g ≃ FamD.rel {x = LiftF.₀ x} {y = LiftF.₀ y} (LiftF.₁ {x} {y} f) (LiftF.₁ {x} {y} g)
    FamF₂-equiv = Sigma.Σ-cong-equiv-snd λ where
      Eq.refl → Equiv.equivΠCod λ j → localEmbedding F is-locally-ff-F (f .snd j) (g .snd j)

    Fam₂-equiv≡LiftF₂ : Equiv.equivFun FamF₂-equiv ≡ LiftF.₂
    Fam₂-equiv≡LiftF₂ = funExt λ { (Eq.refl , rᴰ) → refl }

    goal : isEquiv (LiftF.₂ {x} {y} {f} {g})
    goal = subst isEquiv Fam₂-equiv≡LiftF₂ (Equiv.equivIsEquiv FamF₂-equiv)

  private
    module _ (x* @ (J , x) y* @ (K , y) : FamC.ob) (g* @ (ψ , g) : FamD.hom (LiftF.₀ x*) (LiftF.₀ y*)) where
      hasPointwiseSection→hasLocalSectionFam : (∀ j → Σ[ f ∈ C.hom (x j) (y (ψ j)) ] LocalCatIso D (F.₁ f) (g j)) → Σ[ f* ∈ FamC.hom x* y* ] LocalCatIso (Fam D ℓ) (LiftF.₁ f*) g*
      hasPointwiseSection→hasLocalSectionFam split-F-at = goal where
        f* : Σ[ φ ∈ (⟨ J ⟩ → ⟨ K ⟩) ] ∀ j → C.hom (x j) (y (φ j))
        f* .fst = ψ
        f* .snd = λ j → split-F-at j .fst

        iso-at : LocalCatIso (Fam D ℓ) (LiftF.₁ f*) (ψ , g)
        iso-at .fst = Eq.refl , λ j → split-F-at j .snd .fst
        iso-at .snd .Category.isIso.inv = Eq.refl , λ j → split-F-at j .snd .snd .Category.isIso.inv
        iso-at .snd .Category.isIso.sec = Sigma.ΣPathP (refl , funExt λ j → split-F-at j .snd .snd .Category.isIso.sec)
        iso-at .snd .Category.isIso.ret = Sigma.ΣPathP (refl , funExt λ j → split-F-at j .snd .snd .Category.isIso.ret)

        goal : Σ[ f* ∈ FamC.hom _ _ ] LocalCatIso (Fam D ℓ) (LiftF.₁ f*) (ψ , g)
        goal .fst = f*
        goal .snd = iso-at

  isLocallySplitEssentiallySurjectiveFam : isLocallySplitEssentiallySurjective F → isLocallySplitEssentiallySurjective (LiftFunctor F ℓ)
  isLocallySplitEssentiallySurjectiveFam split-F x y g = hasPointwiseSection→hasLocalSectionFam x y g (λ j → split-F (x .snd j) (y .snd (g .fst j)) (g .snd j))

  isLocallyEssentiallySurjectiveFam : ASC ℓ (ℓ-max ℓh ℓr′) → isLocallyStrict C → isLocallyEssentiallySurjective F → isLocallyEssentiallySurjective (LiftFunctor F ℓ)
  isLocallyEssentiallySurjectiveFam choose is-set-hom-C is-eso-F x*@(J , x) y*@(K , y) g*@(ψ , g) = goal where
    isPointwiseSplitEso : (j : ⟨ J ⟩) → hSet _
    isPointwiseSplitEso j .fst = Σ[ f ∈ C.hom (x j) (y (ψ j)) ] LocalCatIso D (F.₁ f) (g j)
    isPointwiseSplitEso j .snd =  isSetΣ
      (is-set-hom-C (x j) (y (ψ j)))
      λ f → isSetLocalCatIso D (F.₁ f) (g j)

    is-eso-F-at : (j : ⟨ J ⟩) → PT.∥ ⟨ isPointwiseSplitEso j ⟩ ∥₁
    is-eso-F-at j = is-eso-F (x j) (y (ψ j)) (g j)

    merely-ptwise-split-eso : PT.∥ (∀ j → ⟨ isPointwiseSplitEso j ⟩) ∥₁
    merely-ptwise-split-eso = choose J isPointwiseSplitEso is-eso-F-at

    goal : PT.∥ Σ[ f* ∈ FamC.hom x* y* ] LocalCatIso (Fam D ℓ) (LiftF.₁ f*) g* ∥₁
    goal = PT.map (hasPointwiseSection→hasLocalSectionFam x* y* g*) merely-ptwise-split-eso
