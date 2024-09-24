module GpdCont.Bicategory where

open import GpdCont.Prelude hiding (id ; comp ; hcomp ; _◁_ ; _▷_)


private
  variable
   ℓo ℓh ℓr : Level

record Bicategory (ℓo ℓh ℓr : Level) : Type (ℓ-suc (ℓ-max ℓo (ℓ-max ℓh ℓr))) where
  field
    ob : Type ℓo
    hom : (x y : ob) → Type ℓh
    rel : {x y : ob} → (f g : hom x y) → Type ℓr

  field
    is-set-rel : {x y : ob} {f g : hom x y} → isSet (rel f g)

  field
    id : (x : ob) → hom x x
    comp-hom : {x y z : ob} → (f : hom x y) → (g : hom y z) → hom x z

  _·₁_ = comp-hom

  field
    whisker-left : {x y z : ob}
      → (f : hom x y) {g h : hom y z}
      → (α : rel g h)
      → rel (comp-hom f g) (comp-hom f h)

    whisker-right : {x y z : ob}
      → {f g : hom x y} (α : rel f g)
      → (h : hom y z)
      → rel (f ·₁ h) (g ·₁ h)

  _◁_ = whisker-left
  _▷_ = whisker-right
  
  field
    reflexive : {x y : ob} → (f : hom x y) → rel f f
    symmetric : {x y : ob} {f g : hom x y} → (α : rel f g) → rel g f
    transitive : {x y : ob} {f g h : hom x y} → (α : rel f g) → (β : rel g h) → rel f h

  _·₂_ = transitive
  _⁻ = symmetric

  field
    symmetric-inv-left : {x y : ob} {f g : hom x y} (α : rel f g) → (α ⁻) ·₂ α ≡ reflexive g
    symmetric-inv-right : {x y : ob} {f g : hom x y} (α : rel f g) → α ·₂ (α ⁻) ≡ reflexive f

    unitor-left : {x y : ob} (f : hom x y) → rel (id x ·₁ f) f
    unitor-right : {x y : ob} (f : hom x y) → rel (f ·₁ id y) f

    associator : {x y z w : ob} (f : hom x y) (g : hom y z) (h : hom z w) → rel (f ·₁ (g ·₁ h)) ((f ·₁ g) ·₁ h)

  field
    transitive-refl-left : ∀ {x y} (f : hom x y) {g : hom x y}
      → (α : rel f g)
      → reflexive f ·₂ α ≡ α

    transitive-refl-right : ∀ {x y} {f : hom x y} (g : hom x y)
      → (α : rel f g)
      → α ·₂ reflexive g ≡ α

    transitive-assoc : ∀ {x y} (f g h k : hom x y)
      → (α : rel f g) (β : rel g h) (γ : rel h k)
      → α ·₂ (β ·₂ γ) ≡ (α ·₂ β) ·₂ γ

    whisker-left-refl : ∀ {x y z} (f : hom x y) (g : hom y z)
      → f ◁ reflexive g ≡ reflexive (f ·₁ g)
    whisker-right-refl : ∀ {x y z} (f : hom x y) (g : hom y z)
      → reflexive f ▷ g ≡ reflexive (f ·₁ g)

    whisker-left-distr : ∀ {x y z} {g h k : hom y z}
      → (f : hom x y)
      → (α : rel g h) (β : rel h k)
      → f ◁ (α ·₂ β) ≡ (f ◁ α) ·₂ (f ◁ β)
    whisker-right-distr : ∀ {x y z} {f g h : hom x y}
      → (α : rel f g) (β : rel g h)
      → (k : hom y z)
      → (α ·₂ β) ▷ k ≡ (α ▷ k) ·₂ (β ▷ k)
