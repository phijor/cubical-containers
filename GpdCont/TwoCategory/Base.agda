module GpdCont.TwoCategory.Base where

open import GpdCont.Prelude hiding (comp ; hcomp ; _◁_ ; _▷_)

private
  variable
   ℓo ℓh ℓr : Level

module _ {ℓo ℓh ℓr : Level}
  (ob : Type ℓo)
  (hom : (x y : ob) → Type ℓh)
  (rel : {x y : ob} (f g : hom x y) → Type ℓr)
  where

  private
    ℓ = ℓ-max ℓo (ℓ-max ℓh ℓr)

  record TwoCategoryStr : Type ℓ where
    no-eta-equality
    field
      -- Identity 1-cell
      id-hom : (x : ob) → hom x x

      -- Horizontal composition of 1-cells
      comp-hom : {x y z : ob}
        → (f : hom x y)
        → (g : hom y z)
        ---------------
        → hom x z

    field
      -- Vertical identity
      id-rel : {x y : ob} → (f : hom x y) → rel f f

      -- Vertical composition of 2-cells
      trans : {x y : ob}
        → {f g h : hom x y}
        → (r : rel f g)
        → (r : rel g h)
        ---------------
        → rel f h

      -- Horizontal composition of 2-cells
      comp-rel : {x y z : ob}
        → {f₁ f₂ : hom x y} {g₁ g₂ : hom y z}
        → (r : rel f₁ f₂)
        → (s : rel g₁ g₂)
        ---------------------------------------
        → rel (comp-hom f₁ g₁) (comp-hom f₂ g₂)

    _∙₁_ = comp-hom
    _∙ᵥ_ = trans
    _∙ₕ_ = comp-rel

  record IsTwoCategory (s : TwoCategoryStr) : Type ℓ where
    no-eta-equality
    private
      open module s = TwoCategoryStr s

    field
      is-set-rel : {x y : ob} (f g : hom x y) → isSet (rel f g)

    -- Vertical composition is associative and unital
    field
      trans-assoc : {x y : ob}
        → {f g h k : hom x y}
        → (r : rel f g)
        → (s : rel g h)
        → (t : rel h k)
        → (r ∙ᵥ s) ∙ᵥ t ≡ r ∙ᵥ (s ∙ᵥ t)

      trans-unit-left : {x y : ob}
        → {f g : hom x y}
        → (s : rel f g)
        → id-rel f ∙ᵥ s ≡ s

      trans-unit-right : {x y : ob}
        → {f g : hom x y}
        → (r : rel f g)
        → r ∙ᵥ id-rel g ≡ r

    -- Horizontal composition preserves vertical structure (composition and identities)
    field
      comp-rel-id : {x y z : ob}
        → (f : hom x y)
        → (g : hom y z)
        → id-rel (f ∙₁ g) ≡ id-rel f ∙ₕ id-rel g

      comp-rel-trans : {x y z : ob}
        → {f₁ f₂ f₃ : hom x y}
        → {g₁ g₂ g₃ : hom y z}
        → (s : rel f₁ f₂)
        → (t : rel f₂ f₃)
        → (u : rel g₁ g₂)
        → (v : rel g₂ g₃)
        → (s ∙ᵥ t) ∙ₕ (u ∙ᵥ v) ≡ (s ∙ₕ u) ∙ᵥ (t ∙ₕ v)

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

    -- Horizontal composition of 2-cells is associative and unital
    field
      comp-rel-assoc : {x y z w : ob}
        → {f₁ f₂ : hom x y}
        → {g₁ g₂ : hom y z}
        → {k₁ k₂ : hom z w}
        → (s : rel f₁ f₂)
        → (t : rel g₁ g₂)
        → (u : rel k₁ k₂)
        → PathP (λ i → rel (comp-hom-assoc f₁ g₁ k₁ i) (comp-hom-assoc f₂ g₂ k₂ i))
          ((s ∙ₕ t) ∙ₕ u)
          (s ∙ₕ (t ∙ₕ u))

      comp-rel-unit-left : {x y : ob}
        → {f g : hom x y}
        → (s : rel f g)
        → PathP (λ i → rel (comp-hom-unit-left f i) (comp-hom-unit-left g i))
          (id-rel (id-hom x) ∙ₕ s)
          s

      comp-rel-unit-right : {x y : ob}
        → {f g : hom x y}
        → (r : rel f g)
        → PathP (λ i → rel (comp-hom-unit-right f i) (comp-hom-unit-right g i))
          (r ∙ₕ id-rel (id-hom y))
          r

  record LocalGroupoidStr (s : TwoCategoryStr) : Type ℓ where
    no-eta-equality
    private
      open module s = TwoCategoryStr s

    field
      -- Vertical inverse of 2-cells
      inv : {x y : ob}
        → {f g : hom x y}
        → (r : rel f g)
        ---------------
        → rel g f

    -- Inverses cancel
    field
      inv-cancel-left : {x y : ob}
        → {f g : hom x y}
        → (r : rel f g)
        → inv r ∙ᵥ r ≡ id-rel g

      inv-cancel-right : {x y : ob}
        → {f g : hom x y}
        → (r : rel f g)
        → r ∙ᵥ inv r ≡ id-rel f


record TwoCategory (ℓo ℓh ℓr : Level) : Type (ℓ-suc (ℓ-max ℓo (ℓ-max ℓh ℓr))) where
  no-eta-equality
  field
    ob : Type ℓo
    hom : (x y : ob) → Type ℓh
    rel : {x y : ob} → (f g : hom x y) → Type ℓr

  field
    two-category-structure : TwoCategoryStr ob hom rel
    is-two-category : IsTwoCategory ob hom rel two-category-structure

  open TwoCategoryStr two-category-structure public
  open IsTwoCategory is-two-category public

