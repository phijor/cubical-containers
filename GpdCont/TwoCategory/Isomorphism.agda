module GpdCont.TwoCategory.Isomorphism where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LocalCategory

open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Properties
open import Cubical.Categories.Category.Base using (isIso)

private
  variable
    ℓo ℓh ℓr : Level

module Isomorphism (C : TwoCategory ℓo ℓh ℓr) where
  private
    module C = TwoCategory C
    variable
      x y : C.ob
      f : C.hom x y
      g : C.hom y x
      r : C.rel f g
      s : C.rel g f

  record Inverse (f : C.hom x y) (g : C.hom y x) : Type ℓh where
    field
      dom-id : f C.∙₁ g ≡ C.id-hom x
      codom-id : g C.∙₁ f ≡ C.id-hom y

  IsomorphismStr : (f : C.hom x y) → Type ℓh
  IsomorphismStr f = Σ[ g ∈ C.hom _ _ ] Inverse f g

  Isomorphism : (x y : C.ob) → Type ℓh
  Isomorphism x y = Σ[ f ∈ C.hom x y ] IsomorphismStr f

module LocalIso (C : TwoCategory ℓo ℓh ℓr) where
  private
    module C = TwoCategory C
    variable
      x y : C.ob
      f : C.hom x y
      g : C.hom y x
      r : C.rel f g
      s : C.rel g f

  record isLocalInverse {f g : C.hom x y} (r : C.rel f g) (s : C.rel g f) : Type ℓr where
    field
      dom-id : r C.∙ᵥ s ≡ C.id-rel f
      codom-id : s C.∙ᵥ r ≡ C.id-rel g

  unquoteDecl isLocalInverse-Iso-Σ = declareRecordIsoΣ isLocalInverse-Iso-Σ (quote isLocalInverse)

  instance
    isLocalIsoToΣ : RecordToΣ (isLocalInverse r s)
    isLocalIsoToΣ = toΣ isLocalInverse-Iso-Σ

  isPropIsLocalInverse : isProp (isLocalInverse r s)
  isPropIsLocalInverse = recordIsOfHLevel 1 (isProp× (C.is-set-rel _ _ _ _) (C.is-set-rel _ _ _ _))

  hasLocalInverse : (r : C.rel f g) → Type ℓr
  hasLocalInverse r = Σ[ s ∈ C.rel _ _ ] isLocalInverse r s

  isPropHasLocalInverse : isProp (hasLocalInverse r)
  isPropHasLocalInverse {r} (s , s-inv) (s′ , s′-inv) = goal where
    open C

    s≡s′ : s ≡ s′
    s≡s′ =
      s               ≡⟨ sym $ trans-unit-left s ⟩
      id-rel _ ∙ᵥ s   ≡⟨ sym $ cong (_∙ᵥ s) (s′-inv .isLocalInverse.codom-id) ⟩
      (s′ ∙ᵥ r) ∙ᵥ s  ≡⟨ trans-assoc _ _ _ ⟩
      s′ ∙ᵥ (r ∙ᵥ s)  ≡⟨ cong (s′ ∙ᵥ_) (s-inv .isLocalInverse.dom-id) ⟩
      s′ ∙ᵥ id-rel _  ≡⟨ trans-unit-right s′ ⟩
      s′ ∎

    goal : (s , s-inv) ≡ (s′ , s′-inv)
    goal = Σ≡Prop (λ _ → isPropIsLocalInverse) s≡s′

  LocalIso : (f g : C.hom x y) → Type ℓr
  LocalIso f g = Σ[ r ∈ C.rel f g ] hasLocalInverse r

  isLocallyGroupoidal : Type (ℓ-max ℓo (ℓ-max ℓh ℓr))
  isLocallyGroupoidal = ∀ {x y : C.ob} {f g : C.hom x y} (r : C.rel f g) → hasLocalInverse r

  isLocallyGroupoidal→isLocalCategoryIso : isLocallyGroupoidal → ∀ {x y} {f g : C.hom x y} (r : C.rel f g) → isIso (LocalCategory C x y) r
  isLocallyGroupoidal→isLocalCategoryIso inverses r .isIso.inv = inverses r .fst
  isLocallyGroupoidal→isLocalCategoryIso inverses r .isIso.sec = inverses r .snd .isLocalInverse.codom-id
  isLocallyGroupoidal→isLocalCategoryIso inverses r .isIso.ret = inverses r .snd .isLocalInverse.dom-id

  isPropIsLocallyGroupoidal : isProp isLocallyGroupoidal
  isPropIsLocallyGroupoidal = isPropImplicitΠ4 λ _ _ _ _ → isPropΠ λ _ → isPropHasLocalInverse
