module GpdCont.QuotientContainer.Examples where

open import GpdCont.Prelude
open import GpdCont.QuotientContainer.Base
open import GpdCont.QuotientContainer.Premorphism
open import GpdCont.QuotientContainer.Morphism

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv)
open import Cubical.Foundations.Univalence
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sum

open QCont
open Morphism

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

Id×UPair : QCont ℓ-zero
Id×UPair .Shape = Unit
Id×UPair .Pos _ = Unit ⊎ Bool
Id×UPair .isSymm σ = equivFun σ (inl tt) ≡ inl tt
Id×UPair .is-set-shape = isSetUnit
Id×UPair .is-set-pos _ = isSet⊎ isSetUnit isSetBool
Id×UPair .is-prop-symm _ = isSet⊎ isSetUnit isSetBool _ _
Id×UPair .symm-id _ = refl
Id×UPair .symm-sym σ σ-fix-0 = sym (invEq (equivAdjointEquiv σ) σ-fix-0)
Id×UPair .symm-comp σ τ σ-fix-0 τ-fix-0 = cong (equivFun τ) σ-fix-0 ∙ τ-fix-0

private
  Bool≃Dec : (σ : Bool ≃ Bool) → (idEquiv _ ≡ σ) ⊎ (notEquiv ≡ σ)
  Bool≃Dec = {!BoolReflection.reflectEquiv ∙ₑ univalence!}

swap₀-pos : Premorphism UPair UPair $ id (UPair .Shape)
swap₀-pos .Premorphism.pos-mor _ = id _
swap₀-pos .Premorphism.symm-pres _ = id _
swap₀-pos .Premorphism.symm-pres-natural _ _ = refl

swap₀ : Morphism UPair UPair
swap₀ .Morphism.shape-mor = id (UPair .Shape)
swap₀ .Morphism.pos-equiv = SQ.[ swap₀-pos ]

swap₁-pos : Premorphism UPair UPair $ id (UPair .Shape)
swap₁-pos .Premorphism.pos-mor _ = not
swap₁-pos .Premorphism.symm-pres _ = id _
swap₁-pos .Premorphism.symm-pres-natural _ _ = {! !}

swap₁ : Morphism UPair UPair
swap₁ .Morphism.shape-mor = id (UPair .Shape)
swap₁ .Morphism.pos-equiv = SQ.[ swap₁-pos ]

r : PremorphismEquiv swap₀-pos swap₁-pos
r .PremorphismEquiv.η _ = (notEquiv , tt)
r .PremorphismEquiv.η-comm _ = funExt $ sym ∘ notnot

swap₀≡swap₁ : swap₀ ≡ swap₁
swap₀≡swap₁ i .Morphism.shape-mor = refl i
swap₀≡swap₁ i .Morphism.pos-equiv = pre-morphism-eq/ r i
