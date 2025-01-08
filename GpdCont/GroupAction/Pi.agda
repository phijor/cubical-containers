{-# OPTIONS --lossy-unification #-}
module GpdCont.GroupAction.Pi where

open import GpdCont.Prelude
open import GpdCont.GroupAction.Base
open import GpdCont.Equiv using (equivΠCodComp)
open import GpdCont.HomotopySet using (ΠSet ; ΣSet ; _→Set_)
open import GpdCont.GroupAction.Category
open import GpdCont.GroupAction.Equivariant using (isEquivariantMap[_][_,_])
import      GpdCont.Categories.Products as CatProducts
import      GpdCont.Categories.Coproducts as CatCoproducts

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (preCompEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (flip)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (GroupHom≡)
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)
open import Cubical.Categories.Category.Base

private
  variable
    ℓ : Level
    G : Group ℓ
    X : hSet ℓ

open Action using (action ; pres·)

ΠActionΣ : ∀ {ℓG ℓS} (S : hSet ℓS)
  → (X : ⟨ S ⟩ → hSet ℓ)
  → {G : ⟨ S ⟩ → Group ℓG}
  → (∀ s → Action (G s) (X s))
  → Action (ΠGroup G) (ΣSet S X)
ΠActionΣ S X {G} σ = act where
  open module G {s : ⟨ S ⟩} = GroupStr (str (G s)) using (_·_)

  ΠG = ∀ s → ⟨ G s ⟩
  ΣX = Σ[ s ∈ ⟨ S ⟩ ] ⟨ X s ⟩

  Σσ : (g : ΠG) → ΣX ≃ ΣX
  Σσ g = Σ-cong-equiv-snd λ s → σ s .action (g s)

  Σσ-pres·-ext : ∀ (g h : ΠG) (s : ⟨ S ⟩) → (σ s ⁺ (g s · h s)) ≡ (σ s ⁺ h s) ∘ (σ s ⁺ g s)
  Σσ-pres·-ext g h s = cong equivFun (σ s .pres· (g s) (h s))

  Σσ-pres· : ∀ g h → Σσ (λ s → g s · h s) ≡ Σσ g ∙ₑ Σσ h
  Σσ-pres· g h = equivEq λ { i (s , x) → s , Σσ-pres·-ext g h s i x }

  act : Action _ _
  act .action = Σσ
  act .pres· = Σσ-pres·

ΠAction : ∀ {ℓG ℓS} {S : Type ℓS} {G : S → Group ℓG}
  → (X : S → hSet ℓ)
  → (∀ s → Action (G s) (X s))
  → Action (ΠGroup G) (ΠSet X)
ΠAction {S} {G} X σ = act where
  open module G {s : S} = GroupStr (str (G s)) using (_·_)

  σ* : (g : ∀ s → ⟨ G s ⟩) → (∀ s → ⟨ X s ⟩) ≃ (∀ s → ⟨ X s ⟩)
  σ* g = equivΠCod λ s → σ s .action (g s)

  σ-pres· : ∀ g h → σ* (λ s → g s · h s) ≡ σ* g ∙ₑ σ* h
  σ-pres· g h =
    σ* (λ s → g s · h s) ≡⟨ cong equivΠCod $ funExt (λ s → σ s .pres· (g s) (h s)) ⟩
    equivΠCod (λ s → σ s .action (g s) ∙ₑ σ s .action (h s)) ≡⟨ equivΠCodComp _ _ ⟩
    σ* g ∙ₑ equivΠCod (λ s → σ s .action (h s)) ∎

  act : Action _ _
  act .action = σ*
  act .pres· = σ-pres·

-- Any G-action on X also acts on functions (f : X → Y) by precomposition.
-- Note that in order the respect variance (σ acts on X, which is in a negative
-- position), the action inverts group elements:
--
--    σ*(g) : (X → Y) → (X → Y)
--    σ*(g) = λ f → f ∘ σ(g⁻¹)
preCompAction : ∀ {ℓG ℓX ℓY} {G : Group ℓG} {X : hSet ℓX}
  → (σ : Action G X)
  → (Y : hSet ℓY)
  → Action G (X →Set Y)
preCompAction {G} σ Y = σ* where
  open module G = GroupStr (str G) using (_·_ ; inv)

  σ*-pres· : ∀ g h → (σ ⁺ inv (g · h)) ≡ ((σ ⁺ inv g) ∘ (σ ⁺ inv h))
  σ*-pres· g h =
    (σ ⁺ inv (g · h)) ≡⟨ ActionProperties.action-inv σ _ ⟩
    invEq (action σ (g · h)) ≡⟨ cong invEq (σ .pres· g h) ⟩
    invEq (action σ g ∙ₑ action σ h) ≡⟨⟩
    (invEq (action σ g) ∘ invEq (action σ h)) ≡[ i ]⟨ (ActionProperties.action-inv σ g (~ i)) ∘ (ActionProperties.action-inv σ h (~ i)) ⟩
    ((σ ⁺ inv g) ∘ (σ ⁺ inv h)) ∎

  σ* : Action _ _
  σ* .action g = preCompEquiv $ σ .action $ inv g
  σ* .pres· g h = equivEq $ funExt λ f → cong (f ∘_) $ σ*-pres· g h

private
  module GroupActionBase {ℓ} = Category (GroupActionBase ℓ)
  module GroupAction {ℓ} = Category (GroupAction ℓ)

module Products (K : hSet ℓ) (x* : ⟨ K ⟩ → GroupAction.ob {ℓ}) where
  open CatProducts (GroupAction ℓ) ℓ

  import GpdCont.Categories.StructureOver as Str
  import GpdCont.Categories.ProductCategory as Prod
  import GpdCont.Categories.Opposite as Op

  open import GpdCont.Group.Pi as ΠGroup using (GroupProducts)
  open import GpdCont.Categories.Sets using (SetCoproducts)

  open import Cubical.Categories.Displayed.Constructions.StructureOver using (StructureOver)

  private
    module EquivariantMapStr {ℓ} = StructureOver (EquivariantMapStr ℓ)

    BaseProducts : CatProducts.Products (GroupActionBase ℓ) ℓ
    BaseProducts = Prod.ProductCategoryProduct ℓ (GroupProducts ℓ) (Op.OpProducts (SetCoproducts ℓ))

    module SetCoproducts = CatCoproducts.Notation _ ℓ (SetCoproducts ℓ)
    module GroupProducts = CatProducts.Notation _ ℓ (GroupProducts ℓ)
    module BaseProducts = CatProducts.Notation (GroupActionBase ℓ) ℓ BaseProducts

    G×X* : ∀ k → Group ℓ × hSet ℓ
    G×X* = fst ∘ x*

    G* : ∀ k → Group ℓ
    G* = fst ∘ fst ∘ x*

    X* : ∀ k → hSet ℓ
    X* = snd ∘ fst ∘ x*

    σ* : ∀ k → Action (G* k) (X* k)
    σ* = snd ∘ x*

    Πᴰ : Action (ΠGroup G*) (ΣSet K X*)
    Πᴰ = ΠActionΣ K X* σ*

    module GroupActionProduct = Str.Products (GroupActionBase ℓ) (EquivariantMapStr ℓ) ℓ BaseProducts

    πᴰ : ∀ k → GroupActionBase.Hom[ (ΠGroup G* , ΣSet K X*) , G×X* k ]
    πᴰ k = CatProducts.Notation.π (GroupActionBase ℓ) ℓ BaseProducts K G×X* k

    is-equivariant-πᴰ : ∀ k → isEquivariantMap[ πᴰ k ][ Πᴰ , σ* k ]
    is-equivariant-πᴰ k g = refl

    module _ (H×Y @ (H , Y) : GroupActionBase.ob {ℓ})
      (τ : Action H Y)
      (ψ×g : ∀ k → GroupActionBase.Hom[ H×Y , G×X* k ])
      where
      private
        ψ : (k : ⟨ K ⟩) → GroupHom H (G* k)
        ψ = fst ∘ ψ×g

        g : (k : ⟨ K ⟩) → ⟨ X* k ⟩ → ⟨ Y ⟩
        g = snd ∘ ψ×g

      Π-ψ×g : GroupActionBase.Hom[ H×Y , (ΠGroup G* , ΣSet K X*) ]
      Π-ψ×g = BaseProducts.univ-iso K G×X* H×Y .Iso.inv ψ×g

      Π-ψ×g' : GroupActionBase.Hom[ H×Y , (ΠGroup G* , ΣSet K X*) ]
      Π-ψ×g' .fst = ΠGroup.univ-iso ℓ K G* H .Iso.inv ψ
      Π-ψ×g' .snd = SetCoproducts.univ-iso K X* Y .Iso.inv g

      ψ×g-coherence : Π-ψ×g ≡ Π-ψ×g'
      ψ×g-coherence = ≡-× (ΠGroup.univ-inv-coherence ℓ K G* H ≡$ ψ) refl

      toΠ' : EquivariantMapStr.Hom[ Π-ψ×g' ][ τ , Πᴰ ] → ∀ k → EquivariantMapStr.Hom[ ψ×g k ][ τ , σ* k ]
      toΠ' eqva k h = goal where
        goal : (τ ⁺ h) ∘ (g k) ≡ g k ∘ (σ* k ⁺ ψ k .fst h)
        goal i = λ x → eqva h i (k , x)

      fromΠ' : (∀ k → EquivariantMapStr.Hom[ ψ×g k ][ τ , σ* k ]) → EquivariantMapStr.Hom[ Π-ψ×g' ][ τ , Πᴰ ]
      fromΠ' eqva* h = goal where
        goal : (τ ⁺ h) ∘ (uncurry g) ≡ λ { (k , x) → g k ((σ* k ⁺ ψ k .fst h) x) }
        goal i (k , x) = eqva* k h i x

      opaque
        toΠ : EquivariantMapStr.Hom[ Π-ψ×g ][ τ , Πᴰ ] → ∀ k → EquivariantMapStr.Hom[ ψ×g k ][ τ , σ* k ]
        toΠ = toΠ' ∘ subst EquivariantMapStr.Hom[_][ τ , Πᴰ ] ψ×g-coherence

        fromΠ : (∀ k → EquivariantMapStr.Hom[ ψ×g k ][ τ , σ* k ]) → EquivariantMapStr.Hom[ Π-ψ×g ][ τ , Πᴰ ]
        fromΠ eqva = subst EquivariantMapStr.Hom[_][ τ , Πᴰ ] (sym ψ×g-coherence) (fromΠ' eqva)

  GroupActionProduct : Product K x*
  GroupActionProduct = GroupActionProduct.∫Product K x* Πᴰ is-equivariant-πᴰ
    λ where
      {x} {xᴰ} f .fst → toΠ x xᴰ f
      {x} {xᴰ} f .snd → fromΠ x xᴰ f

GroupActionProducts : CatProducts.Products (GroupAction ℓ) ℓ
GroupActionProducts = Products.GroupActionProduct
