module GpdCont.HomotopyGroup.Equiv where

open import GpdCont.Prelude
open import GpdCont.HomotopyGroup.Base
open import GpdCont.HomotopyGroup.Morphism

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level
    G H : hGroup ℓ

hGroupEquiv : ∀ {ℓG ℓH} (G : hGroup ℓG) (H : hGroup ℓH) → Type (ℓ-max ℓG ℓH)
hGroupEquiv G H = Σ[ α ∈ hGroupHom G H ] isEquiv (hGroupHom.fun {G = G} {H = H} α)

mkHGroupEquiv : ∀ {ℓG ℓH} (G : hGroup ℓG) (H : hGroup ℓH)
  → (e : ⟨ G ⟩ᵗ ≃ ⟨ H ⟩ᵗ)
  → (pres-pt₀ : equivFun e (hGroup.pt₀ G) ≡ hGroup.pt₀ H)
  → hGroupEquiv G H
mkHGroupEquiv G H (e , is-equiv-e) pres-pt₀ .fst = mkHGroupHom G H e pres-pt₀
mkHGroupEquiv G H (e , is-equiv-e) pres-pt₀ .snd = is-equiv-e

isSetHGroupEquiv : ∀ {ℓG ℓH} (G : hGroup ℓG) (H : hGroup ℓH) → isSet (hGroupEquiv G H)
isSetHGroupEquiv G H = isSetΣSndProp (isSetHGroupHom G H) λ (α , _) → isPropIsEquiv α

module hGroupEquiv {ℓG ℓH} (G : hGroup ℓG) (H : hGroup ℓH) (α : hGroupEquiv G H) where
  private
    module G = hGroup G
    module H = hGroup H

  open hGroupHom G H (α .fst) public

  equiv : ⟨ G ⟩ᵗ ≃ ⟨ H ⟩ᵗ
  equiv .fst = fun
  equiv .snd = α .snd

  inv-fun : ⟨ H ⟩ᵗ → ⟨ G ⟩ᵗ
  inv-fun = invEq equiv

  inv : hGroupEquiv H G
  inv = mkHGroupEquiv H G (invEquiv equiv) $ sym (invEq (equivAdjointEquiv equiv) pres-pt₀)

idHGroupEquiv : (G : hGroup ℓ) → hGroupEquiv G G
idHGroupEquiv G = mkHGroupEquiv G G (idEquiv _) refl

compHGroupEquiv : ∀ {ℓG ℓH ℓK} (G : hGroup ℓG) (H : hGroup ℓH) (K : hGroup ℓK)
  → hGroupEquiv G H
  → hGroupEquiv H K
  → hGroupEquiv G K
compHGroupEquiv G H K α β = α⨟β where
  module α = hGroupEquiv G H α
  module β = hGroupEquiv H K β

  α⨟β : hGroupEquiv G K
  α⨟β = mkHGroupEquiv G K (compEquiv α.equiv β.equiv) $ cong β.fun α.pres-pt₀ ∙ β.pres-pt₀

invHGroupEquiv : ∀ {ℓG ℓH} (G : hGroup ℓG) (H : hGroup ℓH) → hGroupEquiv G H → hGroupEquiv H G
invHGroupEquiv G H = hGroupEquiv.inv G H

_≃ᴳ⟨_⟩_ : (X : hGroup ℓ) → (hGroupEquiv X G) → (hGroupEquiv G H) → hGroupEquiv X H
_≃ᴳ⟨_⟩_ {G} {H} X α β = compHGroupEquiv X G H α β

_∎ᴳ : (X : hGroup ℓ) → hGroupEquiv X X
_∎ᴳ = idHGroupEquiv

beginᴳ : (X : hGroup ℓ) → (hGroupEquiv X G) → hGroupEquiv X G
beginᴳ _ α = α

-- _≃ᴳ_by_ : 

infixr 0 _≃ᴳ⟨_⟩_
infix 1 _∎ᴳ
{-# INJECTIVE_FOR_INFERENCE _≃ᴳ⟨_⟩_ #-}
{-# INJECTIVE_FOR_INFERENCE _∎ᴳ #-}
