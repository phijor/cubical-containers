open import GpdCont.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Constructions.StructureOver

module GpdCont.Categories.StructureOver
  {ℓo ℓh ℓoᴰ ℓhᴰ}
  (C : Category ℓo ℓh)
  (S : StructureOver C ℓoᴰ ℓhᴰ)
  where

  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Data.Sigma
  open import Cubical.Categories.Displayed.Base
  open import Cubical.Categories.Constructions.TotalCategory renaming (∫C to ∫)
  import      GpdCont.Categories.Products as CatProducts

  private
    module S = StructureOver S
    Cᴰ = StructureOver→Catᴰ S
    module Cᴰ = Categoryᴰ Cᴰ
    ∫C = ∫ {C = C} Cᴰ
    module ∫C = Category ∫C

  module Products (ℓ)
    (ΠC : CatProducts.Products C ℓ)
    where
    open import GpdCont.HomotopySet
    open import GpdCont.Categories.Products ∫C ℓ

    private
      module C where
        open Category C public
        open CatProducts.Notation C ℓ ΠC public

    module _
      (K : hSet ℓ) (c : ⟨ K ⟩ → ∫C.ob)
      (Πᴰ : S.ob[ C.Π K (fst ∘ c) ])
      (πᴰ : ∀ k → S.Hom[ C.π K (fst ∘ c) k ][ Πᴰ , c k .snd ])
      (Homᴰ↔Π : ∀ {x} {xᴰ : S.ob[ x ]} (f : ∀ k → C.Hom[ x , c k .fst ]) →
        (Cᴰ.Hom[ C.univ-iso K (fst ∘ c) x .Iso.inv f ][ xᴰ , Πᴰ ] → (∀ k → Cᴰ.Hom[ f k ][ xᴰ , c k .snd ]))
          ×
        ((∀ k → Cᴰ.Hom[ f k ][ xᴰ , c k .snd ]) → Cᴰ.Hom[ C.univ-iso K (fst ∘ c) x .Iso.inv f ][ xᴰ , Πᴰ ])
      )
      where
      private
        Π : ∫C.ob
        Π .fst = C.Π K (fst ∘ c)
        Π .snd = Πᴰ

        proj : ∀ k → ∫C.Hom[ Π , c k ]
        proj k .fst = C.π K (fst ∘ c) k
        proj k .snd = πᴰ k

        univ-iso : (x : ∫C.ob) → Iso ∫C.Hom[ x , Π ] (∀ k → ∫C.Hom[ x , c k ])
        univ-iso (x , xᴰ) =
          ∫C.Hom[ (x , xᴰ) , Π ] Iso⟨⟩
          Σ[ f ∈ C.Hom[ x , C.Π K (fst ∘ c) ] ] Cᴰ.Hom[ f ][ xᴰ , Πᴰ ] Iso⟨ invIso $ Σ-cong-iso-fst (invIso $ C.univ-iso K (fst ∘ c) x) ⟩
          Σ[ f ∈ (∀ k → C.Hom[ x , (c k .fst) ]) ] Cᴰ.Hom[ _ ][ xᴰ , Πᴰ ] Iso⟨ Σ-cong-iso-snd Homᴰ-iso ⟩
          Σ[ f ∈ (∀ k → C.Hom[ x , (c k .fst) ]) ] (∀ k → Cᴰ.Hom[ f k ][ xᴰ , c k .snd ]) Iso⟨ invIso Σ-Π-Iso ⟩
          (∀ k → ∫C.Hom[ (x , xᴰ) , c k ]) Iso∎
          where
            Homᴰ-iso : (f : ∀ k → C.Hom[ x , c k .fst ])
              → Iso Cᴰ.Hom[ C.univ-iso K (fst ∘ c) x .Iso.inv f ][ xᴰ , Πᴰ ] (∀ k → Cᴰ.Hom[ f k ][ xᴰ , c k .snd ])
            Homᴰ-iso f = isProp→Iso S.isPropHomᴰ (isPropΠ λ k → S.isPropHomᴰ)
              (Homᴰ↔Π f .fst)
              (Homᴰ↔Π f .snd)

      ∫Product : Product K c
      ∫Product .UniversalElement.vertex = Π
      ∫Product .UniversalElement.element = proj
      ∫Product .UniversalElement.universal x = subst isEquiv
        (funExt λ x → funExt λ k → Σ≡Prop (λ f → S.isPropHomᴰ) refl)
        (isoToIsEquiv (univ-iso x))
