module GpdCont.HomotopyGroup.Equiv where

open import GpdCont.Prelude
open import GpdCont.HomotopyGroup.Base
open import GpdCont.HomotopyGroup.Morphism

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv)
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level
    G H : hGroup ℓ

record hGroupEquiv {ℓ ℓ′} (G : hGroup ℓ) (H : hGroup ℓ′) : Type (ℓ-max ℓ ℓ′) where
  no-eta-equality
  field
    hom : hGroupHom G H
    is-equiv : isEquiv (hGroupHom.fun {G = G} {H = H} hom)

  open hGroupHom hom public

  equiv : ⟨ G ⟩ᵗ ≃ ⟨ H ⟩ᵗ
  equiv .fst = fun
  equiv .snd = is-equiv

  inv-fun : ⟨ H ⟩ᵗ → ⟨ G ⟩ᵗ
  inv-fun = invEq equiv

  inv : hGroupEquiv H G
  inv .hom .hGroupHom.fun = inv-fun
  inv .hom .hGroupHom.pres-pt₀ = sym $ invEq (equivAdjointEquiv equiv) pres-pt₀
  inv .is-equiv = equivIsEquiv (invEquiv equiv)


unquoteDecl hGroupEquivIsoΣ = declareRecordIsoΣ hGroupEquivIsoΣ (quote hGroupEquiv)

instance
  hGroupEquivToΣ : RecordToΣ (hGroupEquiv G H)
  hGroupEquivToΣ = toΣ hGroupEquivIsoΣ

open hGroupEquiv

_≃ᴳ_ : ∀ {ℓG ℓH} (G : hGroup ℓG) (H : hGroup ℓH) → Type (ℓ-max ℓG ℓH)
_≃ᴳ_ = hGroupEquiv

infix 4 _≃ᴳ_

mkHGroupEquiv : ∀ {ℓG ℓH} (G : hGroup ℓG) (H : hGroup ℓH)
  → (e : ⟨ G ⟩ᵗ ≃ ⟨ H ⟩ᵗ)
  → (pres-pt₀ : equivFun e (hGroup.pt₀ G) ≡ hGroup.pt₀ H)
  → hGroupEquiv G H
mkHGroupEquiv G H e pres-pt₀ .hom .hGroupHom.fun = equivFun e
mkHGroupEquiv G H e pres-pt₀ .hom .hGroupHom.pres-pt₀ = pres-pt₀
mkHGroupEquiv G H e pres-pt₀ .is-equiv = equivIsEquiv e

isSetHGroupEquiv : ∀ {ℓG ℓH} (G : hGroup ℓG) (H : hGroup ℓH) → isSet (hGroupEquiv G H)
isSetHGroupEquiv G H = recordIsOfHLevel 2 $ isSetΣSndProp (isSetHGroupHom G H) λ α → isPropIsEquiv (α .hGroupHom.fun)

idHGroupEquiv : (G : hGroup ℓ) → hGroupEquiv G G
idHGroupEquiv G .hom = idHGroupHom G
idHGroupEquiv G .is-equiv = idIsEquiv _

compHGroupEquiv : ∀ {ℓG ℓH ℓK} (G : hGroup ℓG) (H : hGroup ℓH) (K : hGroup ℓK)
  → hGroupEquiv G H
  → hGroupEquiv H K
  → hGroupEquiv G K
compHGroupEquiv G H K α β = α⨟β where
  module α = hGroupEquiv α
  module β = hGroupEquiv β

  α⨟β : hGroupEquiv G K
  α⨟β = mkHGroupEquiv G K (compEquiv α.equiv β.equiv) $ cong β.fun α.pres-pt₀ ∙ β.pres-pt₀

_≃ᴳ⟨_⟩_ : (X : hGroup ℓ) → (hGroupEquiv X G) → (hGroupEquiv G H) → hGroupEquiv X H
_≃ᴳ⟨_⟩_ {G} {H} X α β = compHGroupEquiv X G H α β

_∎ᴳ : (X : hGroup ℓ) → hGroupEquiv X X
_∎ᴳ = idHGroupEquiv

infixr 0 _≃ᴳ⟨_⟩_
infix 1 _∎ᴳ
