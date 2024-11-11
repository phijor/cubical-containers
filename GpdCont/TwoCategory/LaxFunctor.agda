module GpdCont.TwoCategory.LaxFunctor where

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
      no-eta-equality
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

module _ {ℓo ℓh ℓr}
  (C : TwoCategory ℓo ℓh ℓr)
  where
  private
    module C = TwoCategory C

  idLaxFunctor : LaxFunctor C C
  idLaxFunctor .LaxFunctor.F-ob = id _
  idLaxFunctor .LaxFunctor.F-hom = id _
  idLaxFunctor .LaxFunctor.F-rel = id _
  idLaxFunctor .LaxFunctor.F-rel-id = refl
  idLaxFunctor .LaxFunctor.F-rel-trans r s = refl
  idLaxFunctor .LaxFunctor.F-trans-lax f g = C.id-rel _
  idLaxFunctor .LaxFunctor.F-trans-lax-natural r s = C.trans-unit-right _ ∙ sym (C.trans-unit-left _)
  idLaxFunctor .LaxFunctor.F-id-lax x = C.id-rel (C.id-hom x)
  idLaxFunctor .LaxFunctor.F-assoc f g h = goal where
    open C
    Base : (i j : I) → Type _
    Base _ j = C.rel (C.comp-hom-assoc f g h j) (C.comp-hom-assoc f g h j)

    left :
      ((id-rel f) ∙ₕ (id-rel g)) ∙ₕ (id-rel h)
        ≡
      ((C.id-rel (f ∙₁ g)) ∙ₕ (C.id-rel h)) ∙ᵥ (C.id-rel ((f ∙₁ g) ∙₁ h))
    left = {! !}

    goal : PathP (λ i → C.rel (C.comp-hom-assoc f g h i) (C.comp-hom-assoc f g h i))
      (
        (C.id-rel (f C.∙₁ g) C.∙ₕ C.id-rel h)
          C.∙ᵥ
        (C.id-rel ((f C.∙₁ g) C.∙₁ h))
      )
      (
        (C.id-rel f C.∙ₕ C.id-rel (g C.∙₁ h))
          C.∙ᵥ
        (C.id-rel (f C.∙₁ (g C.∙₁ h)))
      )
    goal = doubleCompPathP Base left (C.comp-rel-assoc (C.id-rel f) (C.id-rel g) (C.id-rel h)) {! !}
  idLaxFunctor .LaxFunctor.F-unit-left {x} {y} f = goal where
    goal : PathP (λ i → C.rel (C.comp-hom-unit-left f i) (C.comp-hom-unit-left f i))
      (
        (C.id-rel (C.id-hom x) C.∙ₕ C.id-rel f)
          C.∙ᵥ
        C.id-rel (C.id-hom x C.∙₁ f)
      )
      (C.id-rel f)
    goal = {! !}
  idLaxFunctor .LaxFunctor.F-unit-right = {! !}

private
  variable
    ℓo ℓh ℓr : Level
    C D E : TwoCategory ℓo ℓh ℓr

module _
  (F : LaxFunctor C D)
  (G : LaxFunctor D E)
  where
  private
    module C = TwoCategory C
    module D = TwoCategory D
    module E = TwoCategory E
    module F = LaxFunctor F
    module G = LaxFunctor G

  compLaxFunctor : LaxFunctor C E
  compLaxFunctor .LaxFunctor.F-ob = F.F-ob ⋆ G.F-ob
  compLaxFunctor .LaxFunctor.F-hom = F.F-hom ⋆ G.F-hom
  compLaxFunctor .LaxFunctor.F-rel = F.F-rel ⋆ G.F-rel
  compLaxFunctor .LaxFunctor.F-rel-id = cong G.F-rel F.F-rel-id ∙ G.F-rel-id
  compLaxFunctor .LaxFunctor.F-rel-trans r s = cong G.F-rel (F.F-rel-trans r s) ∙ G.F-rel-trans (F.F-rel r) (F.F-rel s)
  compLaxFunctor .LaxFunctor.F-trans-lax f g = trans-lax where
    F-trans-f-g : D.rel (F.F-hom f D.∙₁ F.F-hom g) (F.F-hom (f C.∙₁ g))
    F-trans-f-g = F.F-trans-lax f g

    G-trans' : E.rel (G.F-hom (F.F-hom f D.∙₁ F.F-hom g)) (G.F-hom (F.F-hom (f C.∙₁ g)))
    G-trans' = G.₂ F-trans-f-g

    trans-lax : E.rel (G.F-hom (F.F-hom f) E.∙₁ G.F-hom (F.F-hom g)) (G.F-hom (F.F-hom (f C.∙₁ g)))
    trans-lax = subst (E.rel _) {! !} (G.F-trans-lax (F.₁ f) (F.₁ g))
  compLaxFunctor .LaxFunctor.F-trans-lax-natural = {! !}
  compLaxFunctor .LaxFunctor.F-id-lax x = {! !} where
    idꟳ : D.rel (D.id-hom (F.F-ob x)) (F.F-hom (C.id-hom x))
    idꟳ = F.F-id-lax x

    idᴳ : E.rel (E.id-hom (G.F-ob (F.₀ x))) (G.F-hom (D.id-hom (F.₀ x)))
    idᴳ = G.F-id-lax (F.₀ x)
  compLaxFunctor .LaxFunctor.F-assoc = {! !}
  compLaxFunctor .LaxFunctor.F-unit-left = {! !}
  compLaxFunctor .LaxFunctor.F-unit-right = {! !}
