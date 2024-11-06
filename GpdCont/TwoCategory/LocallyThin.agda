module GpdCont.TwoCategory.LocallyThin where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.TwoDiscrete

open import Cubical.Foundations.HLevels using (isSet→isGroupoid)
open import Cubical.Categories.Category.Base
open import Cubical.WildCat.Base

private
  variable
    ℓo ℓh ℓr : Level

isLocallyThin : (C : TwoCategory ℓo ℓh ℓr) → Type _
isLocallyThin C = ∀ {x y} (f g : TwoCategory.hom C x y) → isProp (TwoCategory.rel C f g)

module _ (C : TwoCategory ℓo ℓh ℓr) where
  open TwoCategory C

  has-relPathP : Type _
  has-relPathP = ∀ {x y : ob}
    → {f₀ f₁ : hom x y} → {f : PathP (λ i → hom x y) f₀ f₁}
    → {g₀ g₁ : hom x y} → {g : PathP (λ i → hom x y) g₀ g₁}
    → {r : rel f₀ g₀}
    → {s : rel f₁ g₁}
    → PathP (λ i → rel (f i) (g i)) r s

  isLocallyThin→relPathP : isLocallyThin C → has-relPathP
  isLocallyThin→relPathP is-prop-rel {f} {g} {r} {s} = isProp→PathP (λ i → is-prop-rel (f i) (g i)) r s

module _ {ℓo ℓh ℓr : Level}
  (ob : Type ℓo)
  (hom : (x y : ob) → Type ℓh)
  (rel : {x y : ob} (f g : hom x y) → Type ℓr)
  where

  private
    ℓ : Level
    ℓ = ℓMax ℓo ℓh ℓr

  record IsLocallyThinStr (s : TwoCategoryStr ob hom rel) : Type ℓ where
    private
      open module s = TwoCategoryStr s

    field
      is-prop-rel : {x y : ob} (f g : hom x y) → isProp (rel f g)

    -- Horizontal composition of 1-cells is strictly associative and unital
    field
      comp-hom-assoc : {x y z w : ob}
        → (f : hom x y)
        → (g : hom y z)
        → (h : hom z w)
        → (f ∙₁ g) ∙₁ h ≡ f ∙₁ (g ∙₁ h)

      comp-hom-unit-left : {x y : ob}
        → (g : hom x y)
        → id-hom x ∙₁ g ≡ g

      comp-hom-unit-right : {x y : ob}
        → (f : hom x y)
        → f ∙₁ id-hom y ≡ f

    -- Any parallel pair of 2-cells are connected by a (dependent) path
    relPathP : {x y : ob}
      → {f₀ f₁ : hom x y} → {f : PathP (λ i → hom x y) f₀ f₁}
      → {g₀ g₁ : hom x y} → {g : PathP (λ i → hom x y) g₀ g₁}
      → {r : rel f₀ g₀}
      → {s : rel f₁ g₁}
      → PathP (λ i → rel (f i) (g i)) r s
    relPathP {f} {g} {r} {s} = isProp→PathP (λ i → is-prop-rel (f i) (g i)) r s

    toIsTwoCategory : IsTwoCategory ob hom rel s
    toIsTwoCategory .IsTwoCategory.is-set-rel f g = isProp→isSet (is-prop-rel f g)
    toIsTwoCategory .IsTwoCategory.trans-assoc r s t = relPathP
    toIsTwoCategory .IsTwoCategory.trans-unit-left _ = relPathP
    toIsTwoCategory .IsTwoCategory.trans-unit-right _ = relPathP
    toIsTwoCategory .IsTwoCategory.comp-rel-id _ _ = relPathP
    toIsTwoCategory .IsTwoCategory.comp-rel-trans s t u v = relPathP
    toIsTwoCategory .IsTwoCategory.comp-hom-assoc = comp-hom-assoc
    toIsTwoCategory .IsTwoCategory.comp-hom-unit-left = comp-hom-unit-left
    toIsTwoCategory .IsTwoCategory.comp-hom-unit-right = comp-hom-unit-right
    toIsTwoCategory .IsTwoCategory.comp-rel-assoc s t u = relPathP
    toIsTwoCategory .IsTwoCategory.comp-rel-unit-left s = relPathP
    toIsTwoCategory .IsTwoCategory.comp-rel-unit-right r = relPathP

module _
  {ℓoC ℓhC ℓrC}
  {ℓoD ℓhD ℓrD}
  (C : TwoCategory ℓoC ℓhC ℓrC)
  (D : TwoCategory ℓoD ℓhD ℓrD)
  (is-prop-rel : isLocallyThin D)
  where
  private
    ℓ : Level
    ℓ = ℓMax ℓoC ℓhC ℓrC ℓoD ℓhD ℓrD
    module C = TwoCategory C
    module D = TwoCategory D

    relPathP : has-relPathP D
    relPathP = isLocallyThin→relPathP D is-prop-rel

  record IntoLocallyThin : Type ℓ where
    field
      F-ob : C.ob → D.ob
      F-hom : {x y : C.ob} → C.hom x y → D.hom (F-ob x) (F-ob y)
      F-rel : {x y : C.ob} {f g : C.hom x y} → C.rel f g → D.rel (F-hom f) (F-hom g)

    ₀ = F-ob
    ₁ = F-hom
    ₂ = F-rel

    field
      -- Lax functoriality
      F-trans-lax : {x y z : C.ob} (f : C.hom x y) (g : C.hom y z)
        → D.rel (F-hom f D.∙₁ F-hom g) (F-hom (f C.∙₁ g))
      -- Lax unity
      F-id-lax : (x : C.ob) → D.rel (D.id-hom (F-ob x)) (F-hom (C.id-hom x))

    toLaxFunctor : LaxFunctor C D
    toLaxFunctor .LaxFunctor.F-ob = F-ob
    toLaxFunctor .LaxFunctor.F-hom = F-hom
    toLaxFunctor .LaxFunctor.F-rel = F-rel
    toLaxFunctor .LaxFunctor.F-rel-id = relPathP
    toLaxFunctor .LaxFunctor.F-rel-trans _ _ = relPathP
    toLaxFunctor .LaxFunctor.F-trans-lax = F-trans-lax
    toLaxFunctor .LaxFunctor.F-trans-lax-natural r s = relPathP
    toLaxFunctor .LaxFunctor.F-id-lax = F-id-lax
    toLaxFunctor .LaxFunctor.F-assoc _ _ _ = relPathP
    toLaxFunctor .LaxFunctor.F-unit-left _ = relPathP
    toLaxFunctor .LaxFunctor.F-unit-right _ = relPathP

module FromCategory {ℓo ℓh} (C : Category ℓo ℓh) where
  private
    module C = Category C

    C-wild : WildCat ℓo ℓh
    C-wild = record { C }

  LocallyThin : TwoCategory ℓo ℓh ℓh
  LocallyThin = TwoDiscrete C-wild λ x y → isSet→isGroupoid C.isSetHom
