open import GpdCont.Prelude

open import Cubical.Categories.Category.Base
import      GpdCont.Categories.Products as CatProducts

module GpdCont.Categories.ProductCategory {ℓo ℓo′ ℓh ℓh′}
  {C : Category ℓo ℓh}
  {D : Category ℓo′ ℓh′}
  (ℓ : Level)
  (ΠC : CatProducts.Products C ℓ)
  (ΠD : CatProducts.Products D ℓ)
  where

  open import GpdCont.HomotopySet

  open import Cubical.Foundations.Isomorphism
  open import Cubical.Data.Sigma
  open import Cubical.Categories.Constructions.BinProduct using (_×C_)

  private
    C×D = C ×C D
    module C×D = Category C×D

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
