module GpdCont.SymmetricContainer.TwoCategory where

open import GpdCont.Prelude
open import GpdCont.SymmetricContainer.Base
open import GpdCont.SymmetricContainer.Morphism using (idMorphism ; isGroupoidMorphism ; Morphism)
open import GpdCont.SymmetricContainer.WildCat using (Eval ; EvalFunctor ; module EvalFunctor ; SymmContWildCat)
open import GpdCont.SymmetricContainer.Eval using (⟦-⟧-Path ; ⟦-⟧ᵗ-Path ; ⟦_⟧)
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.TwoDiscrete using (TwoDiscrete)
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.StrictFunctor
open import GpdCont.TwoCategory.HomotopyGroupoid using () renaming (hGpdCat to hGpd)
open import GpdCont.TwoCategory.GroupoidEndo using (Endo)
open import GpdCont.WildCat.NatTrans using (WildNatTransPath ; isGroupoidHom→WildNatTransSquare)
open import GpdCont.WildCat.TypeOfHLevel using (idNatTransₗ ; idNatTransᵣ ; hGroupoidNatTransSquare)
open import GpdCont.WildCat.TypeOfHLevel using (idNat ; _⊛_)

open import GpdCont.Polynomial using (poly⟨_,_⟩ ; Polynomial)

import      Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Path using (compPath→Square)
open import Cubical.WildCat.Base using (WildCat)
open import Cubical.WildCat.Functor using (WildFunctor ; WildNatTrans)

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

SymmContCat : (ℓ : Level) → TwoCategory (ℓ-suc ℓ) ℓ ℓ
SymmContCat ℓ = TwoDiscrete (SymmContWildCat ℓ) λ _ _ → isGroupoidMorphism

module ⟦-⟧ {ℓ} where
  private
    module SymmCont = TwoCategory (SymmContCat ℓ)
    module Endo = TwoCategory (Endo ℓ)
    module hGpd = TwoCategory (hGpd ℓ)

  ⟦_⟧₀ = Eval
  ⟦_⟧₁ = EvalFunctor.on-hom

  hom-comp : ∀ {F G H : SymmCont.ob} (f : SymmCont.hom F G) (g : SymmCont.hom G H)
    → ⟦ f ⟧₁ Endo.∙₁ ⟦ g ⟧₁ ≡ ⟦ f SymmCont.∙₁ g ⟧₁
  hom-comp f g = sym (EvalFunctor.on-hom-seq f g)

  hom-id : (F : SymmCont.ob) → Endo.id-hom ⟦ F ⟧₀ ≡ ⟦ SymmCont.id-hom F ⟧₁
  hom-id f = sym EvalFunctor.on-hom-id

  module _ {F G : SymmCont.ob} (f : SymmCont.hom F G) where
    private module f = Morphism f
    unit-left-filler : PathCompFiller (cong (Endo._∙₁ ⟦ f ⟧₁) (hom-id F)) (hom-comp (SymmCont.id-hom F) f)
    unit-left-filler .fst = Endo.comp-hom-unit-left ⟦ f ⟧₁
    unit-left-filler .snd = hGroupoidNatTransSquare ℓ λ X → reflSquare _

    unit-left : PathP (λ i → Endo.comp-hom-unit-left ⟦ f ⟧₁ i ≡ ⟦ f ⟧₁) (Endo.comp-hom-unit-left ⟦ f ⟧₁) (refl′ ⟦ f ⟧₁)
    unit-left i j = Endo.comp-hom-unit-left ⟦ f ⟧₁ (i ∨ j)

    unit-right-filler : PathCompFiller (cong (⟦ f ⟧₁ Endo.∙₁_) (hom-id G)) (hom-comp f (SymmCont.id-hom G))
    unit-right-filler .fst = Endo.comp-hom-unit-right ⟦ f ⟧₁
    unit-right-filler .snd = hGroupoidNatTransSquare ℓ λ X → reflSquare _

    unit-right : PathP (λ i → Endo.comp-hom-unit-right ⟦ f ⟧₁ i ≡ ⟦ f ⟧₁) (Endo.comp-hom-unit-right ⟦ f ⟧₁) (refl′ ⟦ f ⟧₁)
    unit-right i j = Endo.comp-hom-unit-right ⟦ f ⟧₁ (i ∨ j)

  module _ {F G H : SymmCont.ob} (f : SymmCont.hom F G) (g : SymmCont.hom G H) where
    open WildNatTrans
    comp-hom-nat-filler : ∀ {x y} (α : hGpd.hom x y) → (⟦ f ⟧₁ Endo.∙₁ ⟦ g ⟧₁) .N-hom {x} {y} α ≡ refl
    comp-hom-nat-filler α = sym GL.compPathRefl

  module _ {F G H K : SymmCont.ob} (f : SymmCont.hom F G) (g : SymmCont.hom G H) (h : SymmCont.hom H K) where
    open WildNatTrans

    assoc-filler-left : PathCompFiller (cong (Endo._∙₁ ⟦ h ⟧₁) (hom-comp f g)) (hom-comp (f SymmCont.∙₁ g) h)
    assoc-filler-left .fst = WildNatTransPath
      (λ X → refl)
      λ {x} {y} α →
        ((⟦ f ⟧₁ Endo.∙₁ ⟦ g ⟧₁) Endo.∙₁ ⟦ h ⟧₁) .N-hom {x} {y} α ≡[ i ]⟨ ((hom-comp f g i) Endo.∙₁ ⟦ h ⟧₁) .N-hom {x} {y} α ⟩
        (⟦ f SymmCont.∙₁ g ⟧₁ Endo.∙₁ ⟦ h ⟧₁) .N-hom {x} {y} α ≡⟨ comp-hom-nat-filler (f SymmCont.∙₁ g) h {x} {y} α ⟩
        ⟦ (f SymmCont.∙₁ g) SymmCont.∙₁ h ⟧₁ .N-hom {x} {y} α ∎
    assoc-filler-left .snd = hGroupoidNatTransSquare ℓ λ X → reflSquare _

    assoc-filler-right : PathCompFiller (cong (⟦ f ⟧₁ Endo.∙₁_) (hom-comp g h)) (hom-comp f (g SymmCont.∙₁ h))
    assoc-filler-right .fst = WildNatTransPath (λ X → refl)
      λ {x} {y} α →
        (⟦ f ⟧₁ Endo.∙₁ (⟦ g ⟧₁ Endo.∙₁ ⟦ h ⟧₁)) .N-hom {x} {y} α ≡[ i ]⟨ (⟦ f ⟧₁ Endo.∙₁ (hom-comp g h i)) .N-hom {x} {y} α ⟩
        (⟦ f ⟧₁ Endo.∙₁ (⟦ g SymmCont.∙₁ h ⟧₁)) .N-hom {x} {y} α ≡⟨ comp-hom-nat-filler f (g SymmCont.∙₁ h) {x} {y} α ⟩
        ⟦ f SymmCont.∙₁ (g SymmCont.∙₁ h) ⟧₁ .N-hom {x} {y} α ∎
    assoc-filler-right .snd = hGroupoidNatTransSquare ℓ λ X → reflSquare _

    assoc : PathP
      (λ i → Endo.comp-hom-assoc ⟦ f ⟧₁ ⟦ g ⟧₁ ⟦ h ⟧₁ i ≡ ⟦ SymmCont.comp-hom-assoc f g h i ⟧₁)
      (assoc-filler-left .fst)
      (assoc-filler-right .fst)
    assoc = hGroupoidNatTransSquare ℓ λ X → reflSquare _

⟦-⟧ : ∀ {ℓ} → StrictFunctor (SymmContCat ℓ) (Endo ℓ)
⟦-⟧ .StrictFunctor.F-ob = Eval
⟦-⟧ .StrictFunctor.F-hom = EvalFunctor.on-hom
⟦-⟧ .StrictFunctor.F-rel = cong EvalFunctor.on-hom
⟦-⟧ .StrictFunctor.F-rel-id = refl
⟦-⟧ .StrictFunctor.F-rel-trans = GL.cong-∙ EvalFunctor.on-hom
⟦-⟧ .StrictFunctor.F-hom-comp = ⟦-⟧.hom-comp
⟦-⟧ .StrictFunctor.F-hom-id = ⟦-⟧.hom-id
⟦-⟧ .StrictFunctor.F-assoc-filler-left = ⟦-⟧.assoc-filler-left
⟦-⟧ .StrictFunctor.F-assoc-filler-right = ⟦-⟧.assoc-filler-right
⟦-⟧ .StrictFunctor.F-assoc = ⟦-⟧.assoc
⟦-⟧ .StrictFunctor.F-unit-left-filler = ⟦-⟧.unit-left-filler
⟦-⟧ .StrictFunctor.F-unit-left = ⟦-⟧.unit-left
⟦-⟧ .StrictFunctor.F-unit-right-filler = ⟦-⟧.unit-right-filler
⟦-⟧ .StrictFunctor.F-unit-right = ⟦-⟧.unit-right
