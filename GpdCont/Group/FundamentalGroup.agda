module GpdCont.Group.FundamentalGroup where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv.Properties using (conjugatePathEquiv)
open import Cubical.Foundations.HLevels using (hGroupoid)
open import Cubical.Foundations.GroupoidLaws as GL using (assoc ; rUnit ; lUnit ; rCancel ; lCancel)

open import Cubical.Algebra.Group.Base using (Group ; GroupStr ; makeIsGroup)
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv ; IsGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)

module _ {ℓX} (X : hGroupoid ℓX) where
  π₁ : (x₀ : ⟨ X ⟩) → Group ℓX
  π₁ x₀ .fst = x₀ ≡ x₀
  π₁ x₀ .snd .GroupStr.1g = refl
  π₁ x₀ .snd .GroupStr._·_ = _∙_
  π₁ x₀ .snd .GroupStr.inv = sym
  π₁ x₀ .snd .GroupStr.isGroup = makeIsGroup (str X x₀ x₀) assoc (sym ∘ rUnit) (sym ∘ lUnit) rCancel lCancel

  conjugateGroupEquiv : {x y : ⟨ X ⟩} → (p : x ≡ y) → GroupEquiv (π₁ x) (π₁ y)
  conjugateGroupEquiv p .fst = doubleCompPathEquiv p p
  conjugateGroupEquiv {x} {y} p .snd = is-group-hom where abstract
    is-group-hom : IsGroupHom (str (π₁ x)) (sym p ∙∙_∙∙ p) (str (π₁ y))
    is-group-hom = makeIsGroupHom λ (r s : x ≡ x) →
      sym p ∙∙ (r ∙ s) ∙∙ p                 ≡⟨ GL.doubleCompPath-elim' _ _ _ ⟩
      sym p ∙ (r ∙ s) ∙ p                   ≡[ i ]⟨ sym p ∙ (r ∙ lUnit s i) ∙ p ⟩
      sym p ∙ (r ∙ refl ∙ s) ∙ p            ≡[ i ]⟨ sym p ∙ (r ∙ rCancel p (~ i) ∙ s) ∙ p ⟩
      sym p ∙ (r ∙ (p ∙ sym p) ∙ s) ∙ p     ≡[ i ]⟨ sym p ∙ assoc-brace r p (sym p) s i ∙ p ⟩
      sym p ∙ ((r ∙ p) ∙ (sym p ∙ s)) ∙ p   ≡⟨ assoc-brace (sym p) (r ∙ p) (sym p ∙ s) p ⟩
      (sym p ∙ (r ∙ p)) ∙ ((sym p ∙ s) ∙ p) ≡[ i ]⟨ (sym p ∙ (r ∙ p)) ∙ assoc (sym p) s p (~ i) ⟩
      (sym p ∙ r ∙ p) ∙ (sym p ∙ s ∙ p)     ≡⟨ sym $ cong₂ _∙_ (GL.doubleCompPath-elim' _ _ _) (GL.doubleCompPath-elim' _ _ _) ⟩
      (sym p ∙∙ r ∙∙ p) ∙ (sym p ∙∙ s ∙∙ p) ∎
