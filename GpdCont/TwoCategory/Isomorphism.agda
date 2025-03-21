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

  idLocalIso : (f : C.hom x y) → LocalIso f f
  idLocalIso f .fst = C.id-rel f
  idLocalIso f .snd .fst = C.id-rel f
  idLocalIso f .snd .snd .isLocalInverse.dom-id = C.trans-unit-left (C.id-rel f)
  idLocalIso f .snd .snd .isLocalInverse.codom-id = C.trans-unit-right (C.id-rel f)

  pathToLocalIso : {f g : C.hom x y} → f ≡ g → LocalIso f g
  pathToLocalIso {f} = J (λ g p → LocalIso f g) (idLocalIso f)

  private opaque
    cancel-twice : ∀ {f g h : C.hom x y}
      → {r : C.rel f g} {r' : C.rel g f} (p : r C.∙ᵥ r' ≡ C.id-rel _)
      → {s : C.rel g h} {s' : C.rel h g} (q : s C.∙ᵥ s' ≡ C.id-rel _)
      → (r C.∙ᵥ s) C.∙ᵥ (s' C.∙ᵥ r') ≡ C.id-rel _
    cancel-twice {r} {r'} p {s} {s'} q =
      ((r C.∙ᵥ s) C.∙ᵥ (s' C.∙ᵥ r')) ≡⟨ C.trans-assoc r s _ ⟩
      (r C.∙ᵥ (s C.∙ᵥ (s' C.∙ᵥ r'))) ≡⟨ cong (r C.∙ᵥ_) (sym (C.trans-assoc s s' r')) ⟩
      (r C.∙ᵥ ((s C.∙ᵥ s') C.∙ᵥ r')) ≡⟨ cong (λ - → r C.∙ᵥ (- C.∙ᵥ r')) q ⟩
      (r C.∙ᵥ (C.id-rel _ C.∙ᵥ r')) ≡⟨ cong (r C.∙ᵥ_) (C.trans-unit-left r') ⟩
      (r C.∙ᵥ r') ≡⟨ p ⟩
      C.id-rel _ ∎

  compLocalIso : ∀ {f g h : C.hom x y} → LocalIso f g → LocalIso g h → LocalIso f h
  compLocalIso (r , (r' , r-iso)) (s , (s' , s-iso)) .fst = r C.∙ᵥ s
  compLocalIso (r , (r' , r-iso)) (s , (s' , s-iso)) .snd .fst = s' C.∙ᵥ r'
  compLocalIso (r , r' , r-iso) (s , s' , s-iso) .snd .snd .isLocalInverse.dom-id = cancel-twice (r-iso .isLocalInverse.dom-id) (s-iso .isLocalInverse.dom-id)
  compLocalIso (r , r' , r-iso) (s , s' , s-iso) .snd .snd .isLocalInverse.codom-id = cancel-twice (s-iso .isLocalInverse.codom-id) (r-iso .isLocalInverse.codom-id)

  isLocallyGroupoidal : Type (ℓ-max ℓo (ℓ-max ℓh ℓr))
  isLocallyGroupoidal = ∀ {x y : C.ob} {f g : C.hom x y} (r : C.rel f g) → hasLocalInverse r

  isLocallyGroupoidal→isLocalCategoryIso : isLocallyGroupoidal → ∀ {x y} {f g : C.hom x y} (r : C.rel f g) → isIso (LocalCategory C x y) r
  isLocallyGroupoidal→isLocalCategoryIso inverses r .isIso.inv = inverses r .fst
  isLocallyGroupoidal→isLocalCategoryIso inverses r .isIso.sec = inverses r .snd .isLocalInverse.codom-id
  isLocallyGroupoidal→isLocalCategoryIso inverses r .isIso.ret = inverses r .snd .isLocalInverse.dom-id

  isPropIsLocallyGroupoidal : isProp isLocallyGroupoidal
  isPropIsLocallyGroupoidal = isPropImplicitΠ4 λ _ _ _ _ → isPropΠ λ _ → isPropHasLocalInverse
