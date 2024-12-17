open import GpdCont.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base

module GpdCont.Categories.DisplayedOverContr
  {ℓo ℓh ℓoᴰ ℓhᴰ}
  (C : Category ℓo ℓh)
  (Cᴰ : Categoryᴰ C ℓoᴰ ℓhᴰ)
  (contr-ob : isContr (C .Category.ob))
  where

  open import Cubical.Foundations.HLevels
  open import Cubical.Categories.Functor.Base
  open import Cubical.Categories.Constructions.TotalCategory.Base using (∫C)
  open import Cubical.Categories.Equivalence.Base using (_≃ᶜ_)
  open import Cubical.Categories.Equivalence.AdjointEquivalence using (AdjointEquivalence)

  private
    x₀ = contr-ob .fst

    contr-x₀ : ∀ x → x₀ ≡ x
    contr-x₀ = contr-ob .snd

    contr′-x₀ : ∀ {x} → x ≡ x₀
    contr′-x₀ = sym $ contr-x₀ _

    contr-x₀-refl : contr-x₀ x₀ ≡ refl
    contr-x₀-refl = isContr→isProp (isContr→isContrPath contr-ob x₀ x₀) (contr-x₀ x₀) refl

    module C = Category C
    E = C.Hom[ x₀ , x₀ ]
    module Cᴰ = Categoryᴰ Cᴰ

    ob-elim : ∀ {ℓ} {B : C.ob → Type ℓ} → (b₀ : B x₀) → ∀ x → B x
    ob-elim {B} b₀ x = subst B (contr-x₀ x) b₀

    ob-elim-ctr : ∀ {ℓ} (B : C.ob → Type ℓ) (b₀ : B x₀) → ob-elim {B = B} b₀ x₀ ≡ b₀
    ob-elim-ctr B b₀ = cong (λ p → subst B p b₀) contr-x₀-refl ∙ substRefl {B = B} b₀

    ob-elim2 : ∀ {ℓ} {B : (x x′ : C.ob) → Type ℓ} → (b₀ : B x₀ x₀) → ∀ x x′ → B x x′
    ob-elim2 {B} b₀ x x′ = subst2 B (contr-x₀ x) (contr-x₀ x′) b₀

    ob-elim2-ctr : ∀ {ℓ} (B : (x x′ : C.ob) → Type ℓ) (b₀ : B x₀ x₀) → ob-elim2 {B = B} b₀ x₀ x₀ ≡ b₀
    ob-elim2-ctr B b₀ = cong₂ (λ p q → subst2 {w = x₀} B p q b₀) contr-x₀-refl contr-x₀-refl ∙ transportRefl b₀

  ∫ᶜ : Category ℓoᴰ (ℓ-max ℓh ℓhᴰ)
  ∫ᶜ .Category.ob = Cᴰ.ob[ x₀ ]
  ∫ᶜ .Category.Hom[_,_] x y = Σ[ e ∈ E ] Cᴰ.Hom[ e ][ x , y ]
  ∫ᶜ .Category.id .fst = C.id
  ∫ᶜ .Category.id .snd = Cᴰ.idᴰ
  ∫ᶜ .Category._⋆_ (e₁ , fᴰ) (e₂ , gᴰ) .fst = e₁ C.⋆ e₂
  ∫ᶜ .Category._⋆_ (e₁ , fᴰ) (e₂ , gᴰ) .snd = fᴰ Cᴰ.⋆ᴰ gᴰ
  ∫ᶜ .Category.⋆IdL (e , fᴰ) i .fst = C.⋆IdL e i
  ∫ᶜ .Category.⋆IdL (e , fᴰ) i .snd = Cᴰ.⋆IdLᴰ fᴰ i
  ∫ᶜ .Category.⋆IdR (e , fᴰ) i .fst = C.⋆IdR e i
  ∫ᶜ .Category.⋆IdR (e , fᴰ) i .snd = Cᴰ.⋆IdRᴰ fᴰ i
  ∫ᶜ .Category.⋆Assoc (e₁ , fᴰ) (e₂ , gᴰ) (e₃ , hᴰ) i .fst = C.⋆Assoc e₁ e₂ e₃ i
  ∫ᶜ .Category.⋆Assoc (e₁ , fᴰ) (e₂ , gᴰ) (e₃ , hᴰ) i .snd = Cᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ i
  ∫ᶜ .Category.isSetHom = isSetΣ C.isSetHom λ _ → Cᴰ.isSetHomᴰ

  {-
  open Functor

  ∫ᶜ→∫C : Functor ∫ᶜ (∫C Cᴰ)
  ∫ᶜ→∫C .F-ob xᴰ = x₀ , xᴰ
  ∫ᶜ→∫C .F-hom (e , fᴰ) = e , fᴰ
  ∫ᶜ→∫C .F-id = refl
  ∫ᶜ→∫C .F-seq (e₁ , fᴰ) (e₂ , gᴰ) = refl

  ∫C→∫ᶜ : Functor (∫C Cᴰ) ∫ᶜ
  ∫C→∫ᶜ .F-ob = uncurry $ ob-elim {B = λ x → Cᴰ.ob[ x ] → Cᴰ.ob[ x₀ ]} (id _)
  ∫C→∫ᶜ .F-hom = goal _ _ _ _ where
    goal : (x y : C.ob) → (xᴰ : Cᴰ.ob[ x ]) (yᴰ : Cᴰ.ob[ y ])
      → (f : (∫C Cᴰ) [ (x , xᴰ) , (y , yᴰ) ])
      → ∫ᶜ [ ∫C→∫ᶜ .F-ob (x , xᴰ) , ∫C→∫ᶜ .F-ob (y , yᴰ) ]
    goal = ob-elim2 λ xᴰ yᴰ (e , f) → e , subst2 Cᴰ.Hom[ e ][_,_] (sym (hom-elim xᴰ)) (sym (hom-elim yᴰ)) f where
      hom-elim : ∀ xᴰ → ob-elim {B = λ x → Cᴰ.ob[ x ] → Cᴰ.ob[ x₀ ]} (id Cᴰ.ob[ x₀ ]) x₀ xᴰ ≡ xᴰ
      hom-elim = funExt⁻ $ ob-elim-ctr (λ x → Cᴰ.ob[ x ] → Cᴰ.ob[ x₀ ]) (id Cᴰ.ob[ x₀ ])
  ∫C→∫ᶜ .F-id = goal _ _ where
    goal : (x : C.ob) (xᴰ : Cᴰ.ob[ x ]) → ∫C→∫ᶜ .F-hom (∫C Cᴰ .Category.id {x = x , xᴰ}) ≡ ∫ᶜ .Category.id
    goal x xᴰ =
      ∫C→∫ᶜ .F-hom (∫C Cᴰ .Category.id {x = x , xᴰ}) ≡⟨ ob-elim2-ctr (λ x y → ∀ xᴰ yᴰ (f : (∫C Cᴰ) [ (x , xᴰ) , (y , yᴰ) ]) → ∫ᶜ [ ∫C→∫ᶜ .F-ob (x , xᴰ) , ∫C→∫ᶜ .F-ob (y , yᴰ) ]) ? ⟩
      {! !} ≡⟨ {! !} ⟩
      ∫ᶜ .Category.id ∎
  ∫C→∫ᶜ .F-seq = {! !}

  ∫ᶜ-equiv : ∫ᶜ ≃ᶜ ∫C {C = C} Cᴰ
  ∫ᶜ-equiv = AdjointEquivalence.to≃ᶜ {! !}
  -}
