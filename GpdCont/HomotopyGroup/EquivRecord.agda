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

record hGroupEquiv {ℓG ℓH} (G : hGroup ℓG) (H : hGroup ℓH) : Type (ℓ-max ℓG ℓH) where
  -- no-eta-equality
  field
    hom : hGroupHom G H
    is-equiv : isEquiv (hom .fst)

  open module hom = hGroupHom G H hom public

  equiv : ⟨ G ⟩ᵗ ≃ ⟨ H ⟩ᵗ
  equiv .fst = fun
  equiv .snd = is-equiv

  -- inv-fun : ⟨ H ⟩ᵗ → ⟨ G ⟩ᵗ
  -- inv-fun = invEq equiv

  -- inv : hGroupEquiv H G
  -- inv .hom = mkHGroupHom H G (invEq equiv) $ sym (invEq (equivAdjointEquiv equiv) pres-pt₀)
  -- inv .is-equiv = equivIsEquiv (invEquiv equiv)

_≃ᴳ_ : ∀ {ℓG ℓH} → (G : hGroup ℓG) (H : hGroup ℓH) → Type (ℓ-max ℓG ℓH)
_≃ᴳ_ = hGroupEquiv

unquoteDecl hGroupEquivIsoΣ = declareRecordIsoΣ hGroupEquivIsoΣ (quote hGroupEquiv)

instance
  hGroupEquivToΣ : RecordToΣ (hGroupEquiv G H)
  hGroupEquivToΣ = toΣ hGroupEquivIsoΣ

mkHGroupEquiv : ∀ {ℓG ℓH} (G : hGroup ℓG) (H : hGroup ℓH)
  → (e : ⟨ G ⟩ᵗ ≃ ⟨ H ⟩ᵗ)
  → (pres-pt₀ : equivFun e (hGroup.pt₀ G) ≡ hGroup.pt₀ H)
  → hGroupEquiv G H
mkHGroupEquiv G H (e , is-equiv-e) pres-pt₀ .hGroupEquiv.hom = mkHGroupHom G H e pres-pt₀
mkHGroupEquiv G H (e , is-equiv-e) pres-pt₀ .hGroupEquiv.is-equiv = is-equiv-e

isSetHGroupEquiv : ∀ {ℓG ℓH} (G : hGroup ℓG) (H : hGroup ℓH) → isSet (hGroupEquiv G H)
isSetHGroupEquiv G H = recordIsOfHLevel 2 $ isSetΣSndProp (isSetHGroupHom G H) λ (α , _) → isPropIsEquiv α

idHGroupEquiv : (G : hGroup ℓ) → hGroupEquiv G G
idHGroupEquiv G = mkHGroupEquiv G G (idEquiv _) refl

compHGroupEquiv : ∀ {ℓG ℓH ℓK} (G : hGroup ℓG) (H : hGroup ℓH) (K : hGroup ℓK)
  → hGroupEquiv G H
  → hGroupEquiv H K
  → hGroupEquiv G K
compHGroupEquiv G H K α β = α⨟β where
  module α = hGroupEquiv α
  module β = hGroupEquiv β

  α⨟β : hGroupEquiv G K
  α⨟β = mkHGroupEquiv G K (compEquiv α.equiv β.equiv) $ cong β.fun α.pres-pt₀ ∙ β.pres-pt₀

_∙ᴳ_ : ∀ {ℓG ℓH ℓK} {G : hGroup ℓG} {H : hGroup ℓH} {K : hGroup ℓK}
  → hGroupEquiv G H
  → hGroupEquiv H K
  → hGroupEquiv G K
_∙ᴳ_ {G} {H} {K} = compHGroupEquiv G H K
{-# INJECTIVE_FOR_INFERENCE _∙ᴳ_ #-}

invHGroupEquiv : ∀ {ℓG ℓH} (G : hGroup ℓG) (H : hGroup ℓH) → hGroupEquiv G H → hGroupEquiv H G
invHGroupEquiv G H α = mkHGroupEquiv H G (invEquiv α.equiv) pres-pt₀ where
  module α = hGroupEquiv α

  pres-pt₀ : invEq (α.equiv) (hGroup.pt₀ H) ≡ hGroup.pt₀ G
  pres-pt₀ = sym (invEq (equivAdjointEquiv α.equiv) α.pres-pt₀)

_≃ᴳ⟨_⟩_ : (X : hGroup ℓ) → (hGroupEquiv X G) → (hGroupEquiv G H) → hGroupEquiv X H
_≃ᴳ⟨_⟩_ {G} {H} X α β = compHGroupEquiv X G H α β

_∎ᴳ : (X : hGroup ℓ) → hGroupEquiv X X
_∎ᴳ = idHGroupEquiv

beginᴳ : (X : hGroup ℓ) → (hGroupEquiv X G) → hGroupEquiv X G
beginᴳ _ α = α

infixr 0 _≃ᴳ⟨_⟩_
infix 1 _∎ᴳ
{-# INJECTIVE_FOR_INFERENCE _≃ᴳ⟨_⟩_ #-}
{-# INJECTIVE_FOR_INFERENCE _∎ᴳ #-}
