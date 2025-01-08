module GpdCont.TwoCategory.StrictFunctor.Base where

open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
import      Cubical.Foundations.Path as Path
import      Cubical.Foundations.GroupoidLaws as GL

module _ {ℓo ℓo′ ℓh ℓh′ ℓr ℓr′}
  (C : TwoCategory ℓo ℓh ℓr)
  (D : TwoCategory ℓo′ ℓh′ ℓr′)
  where
    private
      ℓ = ℓ-max (ℓ-max ℓo (ℓ-max ℓh ℓr)) (ℓ-max ℓo′ (ℓ-max ℓh′ ℓr′))
      module C = TwoCategory C
      module D = TwoCategory D

    record StrictFunctor : Type ℓ where
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

      -- Strictness constraints
      field
        -- Strict functoriality
        F-hom-comp : {x y z : C.ob} (f : C.hom x y) (g : C.hom y z)
          → (F-hom f D.∙₁ F-hom g) ≡ (F-hom (f C.∙₁ g))
        F-hom-id : (x : C.ob) → D.id-hom (F-ob x) ≡ F-hom (C.id-hom x)

      field
        -- Strict associativity
        -- ====================
        --
        -- The two fillers F-assoc-filler-{left,right} are uniquely determined;
        -- see `GpdCont.Prelude.isContrCompSquareFiller`.  They are here to allow simpler
        -- proofs of `F-assoc`: For some functors these fillers are constant, and as such
        -- the type of `F-assoc` simplifies to a non-dependent path:
        --
        --  flip F-assoc : D.comp-hom-assoc (F₁ f) (F₁ g) (F₁ h) ≡ cong F₁ (C.comp-hom-assoc f g h)
        F-assoc-filler-left : {x y z w : C.ob} (f : C.hom x y) (g : C.hom y z) (h : C.hom z w)
          → PathCompFiller (cong (D._∙₁ F-hom h) (F-hom-comp f g)) (F-hom-comp (f C.∙₁ g) h)

        F-assoc-filler-right : {x y z w : C.ob} (f : C.hom x y) (g : C.hom y z) (h : C.hom z w)
          → PathCompFiller (cong (F-hom f D.∙₁_) (F-hom-comp g h)) (F-hom-comp f (g C.∙₁ h))

        F-assoc : {x y z w : C.ob} (f : C.hom x y) (g : C.hom y z) (h : C.hom z w)
          → PathP (λ i → D.comp-hom-assoc (F-hom f) (F-hom g) (F-hom h) i ≡ F-hom (C.comp-hom-assoc f g h i))
            (F-assoc-filler-left f g h .fst)
            (F-assoc-filler-right f g h .fst)

        -- Strict unitality
        -- ================
        --
        -- Like for associativity, implementations can provide a filler of their own choice.

        -- Strict left-unitality
        F-unit-left-filler : {x y : C.ob} (f : C.hom x y)
          → PathCompFiller (cong (D._∙₁ F-hom f) (F-hom-id x)) (F-hom-comp (C.id-hom x) f)
        F-unit-left : {x y : C.ob} (f : C.hom x y)
          → PathP (λ i → D.comp-hom-unit-left (F-hom f) i ≡ F-hom (C.comp-hom-unit-left f i))
            (F-unit-left-filler f .fst)
            (refl′ (F-hom f))

        -- Strict right-unitality
        F-unit-right-filler : {x y : C.ob} (f : C.hom x y)
          → PathCompFiller (cong (F-hom f D.∙₁_) (F-hom-id y)) (F-hom-comp f (C.id-hom y))
        F-unit-right : {x y : C.ob} (f : C.hom x y)
          → PathP (λ i → D.comp-hom-unit-right (F-hom f) i ≡ F-hom (C.comp-hom-unit-right f i))
              (F-unit-right-filler f .fst)
              (refl′ (F-hom f))

module _ {ℓo ℓh ℓr}
  (C : TwoCategory ℓo ℓh ℓr)
  where
  private
    module C = TwoCategory C

  idStrictFunctor : StrictFunctor C C
  idStrictFunctor .StrictFunctor.F-ob = id _
  idStrictFunctor .StrictFunctor.F-hom = id _
  idStrictFunctor .StrictFunctor.F-rel = id _
  idStrictFunctor .StrictFunctor.F-rel-id = refl
  idStrictFunctor .StrictFunctor.F-rel-trans r s = refl
  idStrictFunctor .StrictFunctor.F-hom-comp f g = refl
  idStrictFunctor .StrictFunctor.F-hom-id x = refl
  idStrictFunctor .StrictFunctor.F-assoc-filler-left f g h .fst = refl′ (C.comp-hom (C.comp-hom f g) h)
  idStrictFunctor .StrictFunctor.F-assoc-filler-left f g h .snd = refl
  idStrictFunctor .StrictFunctor.F-assoc-filler-right f g h .fst = refl′ (C.comp-hom f (C.comp-hom g h))
  idStrictFunctor .StrictFunctor.F-assoc-filler-right f g h .snd = refl
  idStrictFunctor .StrictFunctor.F-assoc f g h = λ i j → C.comp-hom-assoc f g h i
  idStrictFunctor .StrictFunctor.F-unit-left-filler f = refl , refl
  idStrictFunctor .StrictFunctor.F-unit-left f i j = C.comp-hom-unit-left f i
  idStrictFunctor .StrictFunctor.F-unit-right-filler f = refl , refl
  idStrictFunctor .StrictFunctor.F-unit-right f = λ i j → C.comp-hom-unit-right f i

private
  variable
    ℓo ℓh ℓr : Level
    C D E : TwoCategory ℓo ℓh ℓr

module _
  (F : StrictFunctor C D)
  (G : StrictFunctor D E)
  where
  private
    module C = TwoCategory C
    module D = TwoCategory D
    module E = TwoCategory E
    module F = StrictFunctor F
    module G = StrictFunctor G

  compStrictFunctor : StrictFunctor C E
  compStrictFunctor .StrictFunctor.F-ob = F.F-ob ⋆ G.F-ob
  compStrictFunctor .StrictFunctor.F-hom = F.F-hom ⋆ G.F-hom
  compStrictFunctor .StrictFunctor.F-rel = F.F-rel ⋆ G.F-rel
  compStrictFunctor .StrictFunctor.F-rel-id = cong G.F-rel F.F-rel-id ∙ G.F-rel-id
  compStrictFunctor .StrictFunctor.F-rel-trans r s = cong G.F-rel (F.F-rel-trans r s) ∙ G.F-rel-trans (F.F-rel r) (F.F-rel s)
  compStrictFunctor .StrictFunctor.F-hom-comp f g = G.F-hom-comp (F.F-hom f) (F.F-hom g) ∙ cong G.F-hom (F.F-hom-comp f g)
  compStrictFunctor .StrictFunctor.F-hom-id x = G.F-hom-id (F.F-ob x) ∙ cong G.F-hom (F.F-hom-id x)
  compStrictFunctor .StrictFunctor.F-assoc-filler-left f g h = {! !}
  compStrictFunctor .StrictFunctor.F-assoc-filler-right f g h = {! !}
  compStrictFunctor .StrictFunctor.F-assoc f g h = {! !}
  compStrictFunctor .StrictFunctor.F-unit-left-filler f = {! !}
  compStrictFunctor .StrictFunctor.F-unit-left f = {! !}
  compStrictFunctor .StrictFunctor.F-unit-right-filler f = {! !}
  compStrictFunctor .StrictFunctor.F-unit-right f = {! !}
