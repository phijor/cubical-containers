module GpdCont.TwoCategory.Pseudofunctor where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base

module _ {ℓo ℓo′ ℓh ℓh′ ℓr ℓr′}
  (C : TwoCategory ℓo ℓh ℓr)
  (D : TwoCategory ℓo′ ℓh′ ℓr′)
  where
    private
      ℓ = ℓ-max (ℓ-max ℓo (ℓ-max ℓh ℓr)) (ℓ-max ℓo′ (ℓ-max ℓh′ ℓr′))
      module C = TwoCategory C
      module D = TwoCategory D

    record LaxFunctor : Type ℓ where
      field
        F-ob : C.ob → D.ob
        F-hom : {x y : C.ob} → C.hom x y → D.hom (F-ob x) (F-ob y)
        F-rel : {x y : C.ob} {f g : C.hom x y} → C.rel f g → D.rel (F-hom f) (F-hom g)

      ₀ = F-ob
      ₁ = F-hom
      ₂ = F-rel

      -- F-hom is (locally) a functor
      field
        F-rel-id : {x y : C.ob} {f : C.hom x y}
          → F-rel (C.id-rel f) ≡ D.id-rel (F-hom f)
        F-rel-trans : {x y : C.ob} {f g h : C.hom x y}
          → (r : C.rel f g)
          → (s : C.rel g h)
          → F-rel (r C.∙ᵥ s) ≡ (F-rel r) D.∙ᵥ (F-rel s)

      -- Laxity constraints
      field
        -- Lax functoriality
        F-trans-lax : {x y z : C.ob} (f : C.hom x y) (g : C.hom y z)
          → D.rel (F-hom f D.∙₁ F-hom g) (F-hom (f C.∙₁ g))
        F-trans-lax-natural : {x y z : C.ob} {f₁ f₂ : C.hom x y} {g₁ g₂ : C.hom y z}
          → (r : C.rel f₁ f₂)
          → (s : C.rel g₁ g₂)
          → (F-rel r D.∙ₕ F-rel s) D.∙ᵥ F-trans-lax f₂ g₂ ≡ F-trans-lax f₁ g₁ D.∙ᵥ F-rel (r C.∙ₕ s)

        -- Lax unity
        -- NB: This is always natural; it's a transformation of functors 1 ⇉ D (F x) (F x)
        F-id-lax : (x : C.ob) → D.rel (D.id-hom (F-ob x)) (F-hom (C.id-hom x))

      field
        F-assoc : {x y z w : C.ob} (f : C.hom x y) (g : C.hom y z) (h : C.hom z w)
          → PathP (λ i → D.rel (D.comp-hom-assoc (F-hom f) (F-hom g) (F-hom h) i) (F-hom (C.comp-hom-assoc f g h i)))
              ((F-trans-lax f g D.∙ₕ D.id-rel (F-hom h)) D.∙ᵥ F-trans-lax (f C.∙₁ g) h)
              ((D.id-rel (F-hom f) D.∙ₕ F-trans-lax g h) D.∙ᵥ F-trans-lax f (g C.∙₁ h))

        F-unit-left : {x y : C.ob} (f : C.hom x y)
          → PathP (λ i → D.rel (D.comp-hom-unit-left (F-hom f) i) (F-hom (C.comp-hom-unit-left f i)))
              ((F-id-lax x D.∙ₕ D.id-rel (F-hom f)) D.∙ᵥ F-trans-lax (C.id-hom x) f)
              (D.id-rel (F-hom f))

        F-unit-right : {x y : C.ob} (f : C.hom x y)
          → PathP (λ i → D.rel (D.comp-hom-unit-right (F-hom f) i) (F-hom (C.comp-hom-unit-right f i)))
              ((D.id-rel (F-hom f) D.∙ₕ F-id-lax y) D.∙ᵥ F-trans-lax f (C.id-hom y))
              (D.id-rel (F-hom f))
