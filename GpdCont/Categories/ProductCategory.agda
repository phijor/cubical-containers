open import GpdCont.Prelude

open import Cubical.Categories.Category.Base
import      GpdCont.Categories.Products as CatProducts

module GpdCont.Categories.ProductCategory {ℓo ℓo′ ℓh ℓh′}
  {C : Category ℓo ℓh}
  {D : Category ℓo′ ℓh′}
  where

  open import GpdCont.HomotopySet

  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Isomorphism hiding (isIso)
  open import Cubical.Data.Sigma
  open import Cubical.Categories.Constructions.BinProduct using (_×C_)

  private
    C×D = C ×C D
    module C×D = Category C×D

  module _
    (ℓ : Level)
    (ΠC : CatProducts.Products C ℓ)
    (ΠD : CatProducts.Products D ℓ)
    where
    private
      module C where
        open Category C public
        open CatProducts.Notation C ℓ ΠC public

      module D where
        open Category D public
        open CatProducts.Notation D ℓ ΠD public

    module _ (K : hSet ℓ) (xy : ⟨ K ⟩ → C×D.ob) where
      open CatProducts C×D ℓ

      private
        Π : C×D.ob
        Π .fst = C.Π K (fst ∘ xy)
        Π .snd = D.Π K (snd ∘ xy)

      univ-iso : (zw : C×D.ob) → Iso C×D.Hom[ zw , Π ] (∀ k → C×D.Hom[ zw , xy k ])
      univ-iso (z , w) =
        C.Hom[ z , C.Π K (fst ∘ xy) ] × D.Hom[ w , D.Π K (snd ∘ xy) ] Iso⟨ prodIso (C.univ-iso K _ _) (D.univ-iso K _ _) ⟩
        (∀ k → C.Hom[ z , xy k .fst ]) × (∀ k → D.Hom[ w , xy k .snd ]) Iso⟨ invIso Σ-Π-Iso ⟩
        (∀ k → C×D.Hom[ (z , w) , xy k ]) Iso∎

      ProductCategoryProduct : Product K xy
      ProductCategoryProduct .UniversalElement.vertex = C.Π K (fst ∘ xy) , D.Π K (snd ∘ xy)
      ProductCategoryProduct .UniversalElement.element = λ k → C.π K (fst ∘ xy) k , D.π K (snd ∘ xy) k
      ProductCategoryProduct .UniversalElement.universal = isoToIsEquiv ∘ univ-iso

  isUnivalentProductCategory : isUnivalent C → isUnivalent D → isUnivalent C×D
  isUnivalentProductCategory univ-C univ-D .isUnivalent.univ x@(c₁ , d₁) y@(c₂ , d₂) = univ where
    iso-left : (f×g : CatIso C×D x y) → CatIso C c₁ c₂
    iso-left (f×g , is-iso) .fst = f×g .fst
    iso-left (f×g , is-iso) .snd .isIso.inv = is-iso .isIso.inv .fst
    iso-left (f×g , is-iso) .snd .isIso.sec = cong fst (is-iso .isIso.sec)
    iso-left (f×g , is-iso) .snd .isIso.ret = cong fst (is-iso .isIso.ret)

    iso-right : (f×g : CatIso C×D x y) → CatIso D d₁ d₂
    iso-right (f×g , is-iso) .fst = f×g .snd
    iso-right (f×g , is-iso) .snd .isIso.inv = is-iso .isIso.inv .snd
    iso-right (f×g , is-iso) .snd .isIso.sec = cong snd (is-iso .isIso.sec)
    iso-right (f×g , is-iso) .snd .isIso.ret = cong snd (is-iso .isIso.ret)

    fiber-equiv : (f×g : CatIso C×D x y) → (fiber pathToIso (iso-left f×g)) × (fiber pathToIso (iso-right f×g)) ≃ fiber pathToIso f×g
    fiber-equiv f×g =
      {! !}
        ≃⟨ {! !} ⟩
      Σ[ (p , q) ∈ ((c₁ ≡ c₂) × (d₁ ≡ d₂)) ] pathToIso (≡-× p q) ≡ f×g
        ≃⟨ {! !} ⟩
      Σ[ p ∈ x ≡ y ] (pathToIso {C = C×D} p .fst) ≡ f×g .fst
        ≃⟨ Σ-cong-equiv-snd (λ p → Σ≡PropEquiv isPropIsIso) ⟩
      Σ[ p ∈ x ≡ y ] pathToIso p ≡ f×g
        ≃⟨⟩
      fiber pathToIso f×g
        ≃∎

    univ : isEquiv (pathToIso {C = C×D} {x} {y})
    univ .equiv-proof f×g = isOfHLevelRespectEquiv 0 (fiber-equiv f×g)
      (isContrΣ (univ-C .isUnivalent.univ c₁ c₂ .equiv-proof (iso-left f×g)) (λ _ → univ-D .isUnivalent.univ d₁ d₂ .equiv-proof (iso-right f×g)))
