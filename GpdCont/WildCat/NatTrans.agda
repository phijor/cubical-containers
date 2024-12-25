module GpdCont.WildCat.NatTrans where

open import GpdCont.Prelude renaming (id to idfun)

open import Cubical.Foundations.Function using (flip) renaming (_∘_ to _∘fun_)
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.Base using (WildCat ; _[_,_] ; concatMor)
open import Cubical.WildCat.Functor as Functor using (WildFunctor ; WildNatTrans)

private
  variable
    ℓo ℓh : Level
    C D : WildCat ℓo ℓh

open WildCat
open WildFunctor
open WildNatTrans

WildNatTransPath : {F G : WildFunctor C D} {α β : WildNatTrans C D F G}
  → (ob-path : ∀ (x : C .ob) → α .N-ob x ≡ β .N-ob x)
  → (hom-path : ∀ {x y} (f : C [ x , y ])
      → PathP (λ i → (F .F-hom f) ⋆⟨ D ⟩ ob-path y i ≡ ob-path x i ⋆⟨ D ⟩ (G .F-hom f)) (α .N-hom f) (β .N-hom f)
    )
  → α ≡ β
WildNatTransPath ob-path hom-path i .N-ob x = ob-path x i
WildNatTransPath ob-path hom-path i .N-hom f = hom-path f i

WildNatTransSquare : ∀ {ℓo ℓo′ ℓh ℓh′} {C : WildCat ℓo ℓh} {D : WildCat ℓo′ ℓh′} {F G : WildFunctor C D}
  → {α₀₀ α₀₁ : WildNatTrans C D F G}
  → {α₀₋ : α₀₀ ≡ α₀₁}
  → {α₁₀ α₁₁ : WildNatTrans C D F G}
  → {α₁₋ : α₁₀ ≡ α₁₁}
  → {α₋₀ : α₀₀ ≡ α₁₀}
  → {α₋₁ : α₀₁ ≡ α₁₁}
  → (ob-square : ∀ (x : C .ob) → Square (cong N-ob α₀₋ ≡$ x) (cong N-ob α₁₋ ≡$ x) (cong N-ob α₋₀ ≡$ x) (cong N-ob α₋₁ ≡$ x))
  → (hom-square : ∀ {x y} (f : C [ x , y ])
    → SquareP (λ i j → (F .F-hom f) ⋆⟨ D ⟩ (ob-square y i j) ≡ (ob-square x i j) ⋆⟨ D ⟩ (G .F-hom f)) (λ j → α₀₋ j .N-hom f) (λ j → α₁₋ j .N-hom f) (λ i → α₋₀ i .N-hom f) (λ i → α₋₁ i .N-hom f)
    )
  → Square α₀₋ α₁₋ α₋₀ α₋₁
WildNatTransSquare ob-square hom-square i j .N-ob x = ob-square x i j
WildNatTransSquare ob-square hom-square i j .N-hom f = hom-square f i j

isGroupoidHom→WildNatTransSquare : {F G : WildFunctor C D}
  → (∀ {x y} → isGroupoid (D [ x , y ]))
  → {α₀₀ α₀₁ : WildNatTrans C D F G}
  → {α₀₋ : α₀₀ ≡ α₀₁}
  → {α₁₀ α₁₁ : WildNatTrans C D F G}
  → {α₁₋ : α₁₀ ≡ α₁₁}
  → {α₋₀ : α₀₀ ≡ α₁₀}
  → {α₋₁ : α₀₁ ≡ α₁₁}
  → (ob-square : ∀ (x : C .ob) → Square (cong N-ob α₀₋ ≡$ x) (cong N-ob α₁₋ ≡$ x) (cong N-ob α₋₀ ≡$ x) (cong N-ob α₋₁ ≡$ x))
  → Square α₀₋ α₁₋ α₋₀ α₋₁
isGroupoidHom→WildNatTransSquare {C} {D} {F} {G} gpd-hom ob-square = WildNatTransSquare
  ob-square
  λ {x} {y} f → isSet→SquareP
    {A = λ i j → concatMor D (F .F-hom f) (ob-square y i j) ≡ concatMor D (ob-square x i j) (G .F-hom f)}
    (λ i j → gpd-hom _ _)
    _ _ _ _
