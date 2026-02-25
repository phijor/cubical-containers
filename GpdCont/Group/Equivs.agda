module GpdCont.Group.Equivs where

open import GpdCont.Prelude
open import GpdCont.Univalence
open import GpdCont.Group.Solve using (solveGroup)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)

module _ {ℓ} (G : Group ℓ) where
  open GroupStr (str G)
  
  mulRightIso : (g : ⟨ G ⟩) → Iso ⟨ G ⟩ ⟨ G ⟩
  mulRightIso g .Iso.fun = _· g
  mulRightIso g .Iso.inv = _· (inv g)
  mulRightIso g .Iso.sec h = sym (·Assoc h (inv g) g) ∙ cong (h ·_) (·InvL g) ∙ ·IdR h
  mulRightIso g .Iso.ret h = sym (·Assoc h g (inv g)) ∙ cong (h ·_) (·InvR g) ∙ ·IdR h

  mulRightEquiv : (g : ⟨ G ⟩) → ⟨ G ⟩ ≃ ⟨ G ⟩
  mulRightEquiv g = isoToEquiv $ mulRightIso g

  mulRightPath : (g : ⟨ G ⟩) → ⟨ G ⟩ ≡ ⟨ G ⟩
  mulRightPath g = ua $ mulRightEquiv g

  mulLeftIso : (g : ⟨ G ⟩) → Iso ⟨ G ⟩ ⟨ G ⟩
  mulLeftIso g .Iso.fun = g ·_
  mulLeftIso g .Iso.inv = (inv g) ·_
  mulLeftIso g .Iso.sec h = ·Assoc g (inv g) h ∙ cong (_· h) (·InvR g) ∙ ·IdL h
  mulLeftIso g .Iso.ret h = ·Assoc (inv g) g h ∙ cong (_· h) (·InvL g) ∙ ·IdL h

  mulLeftEquiv : (g : ⟨ G ⟩) → ⟨ G ⟩ ≃ ⟨ G ⟩
  mulLeftEquiv g = isoToEquiv $ mulLeftIso g

  mulLeftPath : (g : ⟨ G ⟩) → ⟨ G ⟩ ≡ ⟨ G ⟩
  mulLeftPath g = ua $ mulLeftEquiv g

  conjIso : (g : ⟨ G ⟩) → Iso ⟨ G ⟩ ⟨ G ⟩
  conjIso g = compIso (mulRightIso g) (mulLeftIso (inv g))

  conjEquiv : (g : ⟨ G ⟩) → ⟨ G ⟩ ≃ ⟨ G ⟩
  conjEquiv g = isoToEquiv $ conjIso g

  conjHom : (g : ⟨ G ⟩) → GroupHom G G
  conjHom g .fst = equivFun $ conjEquiv g
  conjHom g .snd = makeIsGroupHom λ (k h : ⟨ G ⟩) →
    inv g · (k · h) · g ≡⟨ rw₁ _ _ _ _ ⟩
    (inv g · k) · (h · g) ≡⟨ cong ((inv g · k) ·_) $ sym (·IdL (h · g)) ⟩
    (inv g · k) · 1g · (h · g) ≡[ i ]⟨ (inv g · k) · ·InvR g (~ i) · (h · g) ⟩
    (inv g · k) · (g · inv g) · (h · g) ≡⟨ rw₂ _ _ _ _ ⟩
    (inv g · k · g) · (inv g · h · g) ∎
    where
      rw₁ : ∀ inv-g k h g → inv-g · (k · h) · g ≡ (inv-g · k) · (h · g)
      rw₁ = solveGroup G

      rw₂ : ∀ inv-g k h g → (inv-g · k) · (g · inv-g) · (h · g) ≡ (inv-g · k · g) · (inv-g · h · g)
      rw₂ = solveGroup G

  conjGroupEquiv : (g : ⟨ G ⟩) → GroupEquiv G G
  conjGroupEquiv g .fst = conjEquiv g
  conjGroupEquiv g .snd = conjHom g .snd

  _ : (g h : ⟨ G ⟩) → equivFun (conjEquiv g) h ≡ (inv g) · h · g
  _ = λ g h → refl
