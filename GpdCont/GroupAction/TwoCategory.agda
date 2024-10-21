{-# OPTIONS --lossy-unification #-}
module GpdCont.GroupAction.TwoCategory where

open import GpdCont.Prelude

open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Category
open import GpdCont.TwoCategory.Base

open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms

module _ (ℓ : Level) where
  private
    module GroupAction = Category (GroupAction ℓ)

    module GroupActionLocal σ τ = LocalCategory {ℓ} σ τ
    -- module Conjugator {σ} {τ} = Category (GroupActionLocal.ConjugatorCat σ τ)

    module ConjugatorAt (σ τ : GroupAction.ob) where
      -- Pattern to turn an equivariant map into an object of the conjugator category
      pattern _′ φ = (tt , φ)

      open module Conjugator = Category (GroupActionLocal.ConjugatorCat σ τ)
        using (Hom[_,_])
        public

      conj : (f g : GroupAction.Hom[ σ , τ ]) → Type _
      conj f g = Hom[ f ′ , g ′ ]

      id-conj : (f : GroupAction.Hom[ σ , τ ]) → conj f f
      id-conj f = Conjugator.id {x = f ′}

      comp-conj : {f g h : GroupAction.Hom[ σ , τ ]} → conj f g → conj g h → conj f h
      comp-conj {f} {g} {h} = Conjugator._⋆_ {x = f ′} {y = g ′} {z = h ′}

      isSetConjugator : (f g : GroupAction.Hom[ σ , τ ]) → isSet (conj f g)
      isSetConjugator f g = Conjugator.isSetHom {x = f ′} {y = g ′}

    -- id-conj : (σ τ : GroupAction.ob) (f : GroupAction.Hom[ σ , τ ]) → Conjugator.Hom[ σ , τ ] [ f ] [ f ]
    -- id-conj σ τ f = Conjugator.id σ τ {x = [ f ]}
    
    module _
      {σ* @ ((G , X) , σ) : GroupAction.ob}
      {τ* @ ((H , Y) , τ) : GroupAction.ob}
      {ρ* @ ((K , Z), ρ) : GroupAction.ob}
      {f₁* @ (((φ₁ , φ₁-hom) , f₁) , f₁-eqva) : GroupAction.Hom[ σ* , τ* ]}
      {f₂* @ (((φ₂ , φ₂-hom) , f₂) , f₂-eqva) : GroupAction.Hom[ σ* , τ* ]}
      {g₁* @ (((ψ₁ , ψ₁-hom) , g₁) , g₁-eqva) : GroupAction.Hom[ τ* , ρ* ]}
      {g₂* @ (((ψ₂ , ψ₂-hom) , g₂) , g₂-eqva) : GroupAction.Hom[ τ* , ρ* ]}
      (h* @ (h , (h-conj-φ₁-φ₂ , h-conj-f₁-f₂)) : ConjugatorAt.conj σ* τ* f₁* f₂*)
      (k* @ (k , (k-conj-ψ₁-ψ₂ , k-conj-g₁-g₂)) : ConjugatorAt.conj τ* ρ* g₁* g₂*)
      where
        private
          open module K = GroupStr (str K) renaming (_·_ to _·ᴷ_)
          open module H = GroupStr (str H) renaming (_·_ to _·ᴴ_)
          _∙ₕ_ = GroupAction._⋆_ {x = σ*} {y = τ*} {z = ρ*}

        h∙ₕk : ⟨ K ⟩
        h∙ₕk = k K.· (ψ₂ h)

        private opaque
          isGroupHomConjugator-k∙ₕk : ∀ g → ψ₁ (φ₁ g) ·ᴷ (k ·ᴷ ψ₂ h) ≡ (k ·ᴷ ψ₂ h) ·ᴷ ψ₂ (φ₂ g)
          isGroupHomConjugator-k∙ₕk g =
            ψ₁ (φ₁ g) ·ᴷ (k ·ᴷ ψ₂ h) ≡⟨ K.·Assoc _ _ _ ⟩
            (ψ₁ (φ₁ g) ·ᴷ k) ·ᴷ ψ₂ h ≡⟨ cong (K._· ψ₂ h) (k-conj-ψ₁-ψ₂ (φ₁ g)) ⟩
            (k ·ᴷ ψ₂ (φ₁ g)) ·ᴷ ψ₂ h ≡⟨ sym $ K.·Assoc _ _ _ ⟩
            k ·ᴷ (ψ₂ (φ₁ g) ·ᴷ ψ₂ h) ≡⟨ cong (k ·ᴷ_) $ sym $ ψ₂-hom .IsGroupHom.pres· (φ₁ g) h ⟩
            k ·ᴷ (ψ₂ (φ₁ g ·ᴴ h))    ≡[ i ]⟨ k ·ᴷ (ψ₂ (h-conj-φ₁-φ₂ g i)) ⟩
            k ·ᴷ (ψ₂ (h ·ᴴ φ₂ g))    ≡⟨ cong (k ·ᴷ_) (ψ₂-hom .IsGroupHom.pres· h (φ₂ g)) ⟩
            k ·ᴷ (ψ₂ h ·ᴷ ψ₂ (φ₂ g)) ≡⟨ K.·Assoc _ _ _ ⟩
            (k ·ᴷ ψ₂ h) ·ᴷ ψ₂ (φ₂ g) ∎

          isMapFiller : (f₁ ∘ g₁) ≡ (f₂ ∘ g₂) ∘ ρ ⁺ (k ·ᴷ ψ₂ h)
          isMapFiller =
            f₁ ∘ g₁                         ≡[ i ]⟨ h-conj-f₁-f₂ i ∘ g₁ ⟩
                -- h is a conjugator of f₁ and f₂
                ----------
            f₂ ∘ τ ⁺ h ∘ g₁                 ≡[ i ]⟨ f₂ ∘ g₁-eqva h i ⟩
                ---------- (g₁ , ψ₁) is equivariant
                ---------------
            f₂ ∘ g₁ ∘ ρ ⁺ (ψ₁ h)            ≡[ i ]⟨ f₂ ∘ (k-conj-g₁-g₂ i) ∘ ρ ⁺ (ψ₁ h) ⟩
                -- h is a conjugator of g₁ and g₂
                ------------
            f₂ ∘ g₂ ∘ (ρ ⁺ k) ∘ ρ ⁺ (ψ₁ h)  ≡[ i ]⟨ f₂ ∘ g₂ ∘ ActionProperties.action-comp ρ (ψ₁ h) k (~ i) ⟩
                      -------------------- ρ preserves composition
                      ---------------
            f₂ ∘ g₂ ∘ ρ ⁺ (ψ₁ h ·ᴷ k)       ≡[ i ]⟨ f₂ ∘ g₂ ∘ ρ ⁺ k-conj-ψ₁-ψ₂ h i ⟩
                          ----------- k is a conjugator of f₁ and f₂
            f₂ ∘ g₂ ∘ ρ ⁺ (k ·ᴷ ψ₂ h) ∎

        compHorizontal : ConjugatorAt.conj σ* ρ* (f₁* ∙ₕ g₁*) (f₂* ∙ₕ g₂*)
        compHorizontal .fst = h∙ₕk
        compHorizontal .snd .fst = isGroupHomConjugator-k∙ₕk
        compHorizontal .snd .snd = isMapFiller

  idCompHorizontal : (σ τ ρ : GroupAction.ob) (f : GroupAction.Hom[ σ , τ ]) (g : GroupAction.Hom[ τ , ρ ])
    → ConjugatorAt.id-conj σ ρ (f GroupAction.⋆ g) ≡
      compHorizontal
        (ConjugatorAt.id-conj σ τ f)
        (ConjugatorAt.id-conj τ ρ g)
  idCompHorizontal ((G , X) , σ) ((H , Y) , τ) ((K , Z) , ρ) f* g*
    using (φ , f) ← GroupActionLocal.homData _ _ f*
    using (ψ , g) ← GroupActionLocal.homData _ _ g*
    = GroupActionLocal.Conjugator≡ _ _ _ _ goal
    where
      open module H = GroupStr (str H) using () renaming (1g to 1ᴴ)
      open module K = GroupStr (str K) using () renaming (1g to 1ᴷ)

      isGroupHom-ψ = g* .fst .fst .snd

      goal : 1ᴷ ≡ 1ᴷ K.· ψ 1ᴴ
      goal = sym $ (K.·IdL (ψ 1ᴴ)) ∙ isGroupHom-ψ .IsGroupHom.pres1

  GroupAction₂ : TwoCategory (ℓ-suc ℓ) ℓ ℓ
  GroupAction₂ .TwoCategory.ob = GroupAction.ob
  GroupAction₂ .TwoCategory.hom = GroupAction.Hom[_,_]
  GroupAction₂ .TwoCategory.rel {x = σ} {y = τ} = ConjugatorAt.conj σ τ
  GroupAction₂ .TwoCategory.two-category-structure = two-cat-str where
    two-cat-str : TwoCategoryStr _ _ _
    two-cat-str .TwoCategoryStr.id-hom σ = GroupAction.id {x = σ}
    -- Horizontal composition of equivariant maps
    two-cat-str .TwoCategoryStr.comp-hom = GroupAction._⋆_
    -- Identity 2-cells: every equivariant map is conjugate to itself
    two-cat-str .TwoCategoryStr.id-rel {x = σ} {y = τ} = ConjugatorAt.id-conj σ τ
    -- Vertical composition of 2-cells: conjugators compose by multiplication
    two-cat-str .TwoCategoryStr.trans {x = σ} {y = τ} = ConjugatorAt.comp-conj σ τ
    -- Horizontal composition of conjugators
    two-cat-str .TwoCategoryStr.comp-rel = compHorizontal
  GroupAction₂ .TwoCategory.is-two-category = is-two-cat where
    is-two-cat : IsTwoCategory _ _ _ _
    is-two-cat .IsTwoCategory.is-set-rel {x = σ} {y = τ} = ConjugatorAt.isSetConjugator σ τ
    is-two-cat .IsTwoCategory.trans-assoc = ConjugatorAt.Conjugator.⋆Assoc _ _
    is-two-cat .IsTwoCategory.trans-unit-left = ConjugatorAt.Conjugator.⋆IdL _ _
    is-two-cat .IsTwoCategory.trans-unit-right = ConjugatorAt.Conjugator.⋆IdR _ _
    is-two-cat .IsTwoCategory.comp-rel-id = idCompHorizontal _ _ _
    is-two-cat .IsTwoCategory.comp-rel-trans {y = ((H , Y) , τ)} {z = ((K , Z) , ρ)} {g₂ = g₂*} {g₃ = g₃*}
      (h₁ , _)
      (h₂ , _)
      (k₁ , _)
      (k₂ , (k₂-cong-hom , _))
      using (ψ₂ , g₂) ← GroupActionLocal.homData _ _ g₂*
      using (ψ₃ , g₃) ← GroupActionLocal.homData _ _ g₃*
      using is-hom-ψ₃ ← GroupActionLocal.hom→isGroupHom _ _ g₃*
      = GroupActionLocal.Conjugator≡ _ _ _ _ goal where
        module H = GroupStr (str H)
        module K = GroupStr (str K)
        goal : (k₁ K.· k₂) K.· ψ₃ (h₁ H.· h₂) ≡ (k₁ K.· ψ₂ h₁) K.· (k₂ K.· (ψ₃ h₂))
        goal =
          (k₁ K.· k₂) K.· ψ₃ (h₁ H.· h₂)    ≡[ i ]⟨ (k₁ K.· k₂) K.· is-hom-ψ₃ .IsGroupHom.pres· h₁ h₂ i ⟩
          (k₁ K.· k₂) K.· (ψ₃ h₁ K.· ψ₃ h₂) ≡⟨ {! !} ⟩
          k₁ K.· (k₂ K.· ψ₃ h₁) K.· ψ₃ h₂   ≡[ i ]⟨ k₁ K.· k₂-cong-hom h₁ (~ i) K.· ψ₃ h₂ ⟩
          k₁ K.· (ψ₂ h₁ K.· k₂) K.· ψ₃ h₂   ≡[ i ]⟨ {! !} ⟩
          (k₁ K.· ψ₂ h₁) K.· (k₂ K.· (ψ₃ h₂)) ∎
    is-two-cat .IsTwoCategory.comp-hom-assoc = GroupAction.⋆Assoc
    is-two-cat .IsTwoCategory.comp-hom-unit-left = GroupAction.⋆IdL
    is-two-cat .IsTwoCategory.comp-hom-unit-right = GroupAction.⋆IdR
    is-two-cat .IsTwoCategory.comp-rel-assoc = {! !}
    is-two-cat .IsTwoCategory.comp-rel-unit-left = {! !}
    is-two-cat .IsTwoCategory.comp-rel-unit-right = {! !}
