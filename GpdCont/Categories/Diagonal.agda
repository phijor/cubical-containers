open import GpdCont.Prelude

open import Cubical.Categories.Category.Base

module GpdCont.Categories.Diagonal {ℓo ℓh} (C : Category ℓo ℓh) (ℓ : Level) where

open import GpdCont.HomotopySet as HSet
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable
private
  module C where
    open Category C public

ΠC : (K : hSet ℓ) → Category _ _
ΠC K .Category.ob = ⟨ K ⟩ → C.ob
ΠC K .Category.Hom[_,_] x y = ∀ k → C.Hom[ x k , y k ]
ΠC K .Category.id k = C.id
ΠC K .Category._⋆_ f g = λ k → f k C.⋆ g k
ΠC K .Category.⋆IdL f = funExt $ C.⋆IdL ∘ f
ΠC K .Category.⋆IdR f = funExt $ C.⋆IdR ∘ f
ΠC K .Category.⋆Assoc f g h = funExt λ k → C.⋆Assoc (f k) (g k) (h k)
ΠC K .Category.isSetHom = isSetΠ λ k → C.isSetHom

Δ : (K : hSet ℓ) → Functor C (ΠC K)
Δ K = ΔK where
  ΔK : Functor _ _
  ΔK .Functor.F-ob c = const c
  ΔK .Functor.F-hom f = const f
  ΔK .Functor.F-id = refl
  ΔK .Functor.F-seq _ _ = refl

isUnivalentΠ : isUnivalent C → ∀ K → isUnivalent (ΠC K)
isUnivalentΠ univ-C K .isUnivalent.univ x y = equivIsEquiv (univ-equiv x y) where
  open isUnivalent univ-C

  module _ (x y : ⟨ K ⟩ → C.ob) where
    iso-at : (f : CatIso (ΠC K) x y) → ∀ k → CatIso C (x k) (y k)
    iso-at (f , f-iso) k .fst = f k
    iso-at (f , f-iso) k .snd = isiso (f-iso .isIso.inv k) (f-iso .isIso.sec ≡$ k) (f-iso .isIso.ret ≡$ k)

    fiber-equiv : (f : CatIso (ΠC K) x y) → (∀ (k : ⟨ K ⟩) → fiber (pathToIso {C = C}) (iso-at f k)) ≃ fiber (pathToIso {C = ΠC K} {x} {y}) f
    fiber-equiv f =
      (∀ (k : ⟨ K ⟩) → fiber (pathToIso {C = C}) (iso-at f k))
        ≃⟨⟩
      (∀ (k : ⟨ K ⟩) → Σ[ p ∈ (x k ≡ y k) ] (pathToIso {C = C} p) ≡ (iso-at f k))
        ≃⟨ equivΠCod (λ k → Σ-cong-equiv-snd λ p → invEquiv (Σ≡PropEquiv isPropIsIso)) ⟩
      (∀ (k : ⟨ K ⟩) → Σ[ p ∈ (x k ≡ y k) ] (pathToIso {C = C} p .fst) ≡ (f .fst k))
        ≃⟨⟩
      (∀ (k : ⟨ K ⟩) → Σ[ p ∈ (x k ≡ y k) ] (subst (λ y → C.Hom[ x k , y ]) p C.id) ≡ (f .fst k))
        ≃⟨ Σ-Π-≃ ⟩
      Σ[ p ∈ (∀ k → x k ≡ y k) ] (∀ k → (subst (λ y → C.Hom[ x k , y ]) (p k) C.id) ≡ (f .fst k))
        ≃⟨ Σ-cong-equiv-snd (λ p → {!lemma !}) ⟩
      Σ[ p ∈ (∀ k → x k ≡ y k) ] (∀ k → (pathToIso {C = ΠC K} (funExt p) .fst k) ≡ (f .fst k))
        ≃⟨ Σ-cong-equiv-snd (λ p → funExtEquiv) ⟩
      Σ[ p ∈ (∀ k → x k ≡ y k) ] Path (ΠC K [ x , y ]) (pathToIso {C = ΠC K} (funExt p) .fst) (f .fst)
        ≃⟨ Σ-cong-equiv-snd (λ p → Σ≡PropEquiv isPropIsIso) ⟩
      Σ[ p ∈ (∀ k → x k ≡ y k) ] pathToIso (funExt p) ≡ f
        ≃⟨ Σ-cong-equiv-fst funExtEquiv ⟩
      Σ[ p ∈ x ≡ y ] pathToIso p ≡ f
        ≃⟨⟩
      fiber (pathToIso {C = ΠC K} {x} {y}) f
        ≃∎

      where
        lemma : (p : ∀ k → x k ≡ y k) → ∀ k → pathToIso {C = ΠC K} (funExt p) .fst k ≡ subst (λ y → C.Hom[ x k , y ]) (p k) C.id
        lemma p k i = {!transp (λ j → C.Hom[ x (transportRefl k (~ j)) , p (transportRefl k (~ j)) i ]) i !}

    univ-equiv : (x ≡ y) ≃ (CatIso (ΠC K) x y)
    univ-equiv .fst = pathToIso
    univ-equiv .snd .equiv-proof f = isOfHLevelRespectEquiv 0 (fiber-equiv f)
      (isContrΠ λ k → univ-C .isUnivalent.univ (x k) (y k) .equiv-proof (iso-at f k))
