module GpdCont.HomotopyGroup.Morphism where

open import GpdCont.Prelude
open import GpdCont.Prelude.Square

open import GpdCont.Equiv
open import GpdCont.HomotopyGroup.Base

open import Cubical.Foundations.Pointed using (_→∙_)

private
  variable
    ℓ ℓ′ : Level

record hGroupHom (G : hGroup ℓ) (H : hGroup ℓ′) : Type (ℓ-max ℓ ℓ′) where
  constructor mkHGroupHom
  no-eta-equality
  field
    fun : ⟨ G ⟩ᵗ → ⟨ H ⟩ᵗ
    pres-pt₀ : fun (hGroup.pt₀ G) ≡ hGroup.pt₀ H


unquoteDecl hGroupHomIsoΣ = declareRecordIsoΣ hGroupHomIsoΣ (quote hGroupHom)

instance
  hGroupHomToΣ : ∀ {G : hGroup ℓ} {H : hGroup ℓ′} → RecordToΣ (hGroupHom G H)
  hGroupHomToΣ = toΣ hGroupHomIsoΣ

open hGroupHom

{-
hGroupHom : (G : hGroup ℓ) (H : hGroup ℓ′) → Type _
hGroupHom (G , _) (H , _) = StrictFun G H

module hGroupHom {ℓ} {ℓ′} (G : hGroup ℓ) (H : hGroup ℓ′) (φ : hGroupHom G H) where
  private
    module G = hGroup G
    module H = hGroup H

  open Σ φ public renaming (fst to fun ; snd to pres-pt)

  pres-pt₀ : fun G.pt₀ ≡ H.pt₀
  pres-pt₀ = sym (pres-pt ≡$ G.center) ∙ cong H.pt (isContr→isProp H.is-connected (ST.map fun G.center) H.center)
-}

module _ {ℓ} {ℓ′} (G : hGroup ℓ) (H : hGroup ℓ′) where
  private
    module G = hGroup G
    module H = hGroup H

    isSetHGroupHom' : isSet (G.asPointed →∙ H.asPointed)
    isSetHGroupHom' (φ , φ-pres-pt) (ψ , ψ-pres-pt) p q = ΣSquarePSet (λ φ → H.is-groupoid (φ G.pt₀) H.pt₀) (funExtSquare goal)
      where
        goal₀ : (λ j → p j .fst G.pt₀) ≡ (λ j → q j .fst G.pt₀)
        goal₀ i j = hcomp {φ = ∂ i ∨ ∂ j}
          (λ where
            k (i = i0) → p j .snd (~ k)
            k (i = i1) → q j .snd (~ k)
            k (j = i0) → φ-pres-pt (~ k)
            k (j = i1) → ψ-pres-pt (~ k)
          )
          H.pt₀

        goal : ∀ g → (λ j → p j .fst g) ≡ (λ j → q j .fst g)
        goal = G.elimProp (λ g → isGroupoid→isPropSquare H.is-groupoid) goal₀

  hGroupHomEquiv : (G.asPointed →∙ H.asPointed) ≃ (hGroupHom G H)
  hGroupHomEquiv = Σ≃ _

  isSetHGroupHom : isSet (hGroupHom G H)
  isSetHGroupHom = recordIsOfHLevel 2 isSetHGroupHom'

  hGroupHom≡ :
    ∀ {φ ψ : hGroupHom G H}
    → (p : φ .fun ≡ ψ .fun)
    → PathP (λ i → p i G.pt₀ ≡ H.pt₀) (φ .pres-pt₀) (ψ .pres-pt₀)
    → φ ≡ ψ
  hGroupHom≡ p q i .fun = p i
  hGroupHom≡ p q i .pres-pt₀ = q i

{-
  hGroupHomStrEquiv : (φ : ⟨ G ⟩ᵗ → ⟨ H ⟩ᵗ) → (φ G.pt₀ ≡ H.pt₀) ≃ (StrictFunStr (G .fst) (H .fst) φ)
  hGroupHomStrEquiv φ =
    (φ G.pt₀ ≡ H.pt₀) ≃⟨ compPathrEquiv $ cong H.pt (isContr→isProp H.is-connected H.center (ST.map φ G.center)) ⟩
    (φ G.pt₀ ≡ H.pt (ST.map φ G.center)) ≃⟨ symEquiv ⟩
    (H.pt (ST.map φ G.center) ≡ φ G.pt₀) ≃⟨ G.centerElimEquiv ⟩
    ((x : G.Tr) → H.pt (ST.map φ x) ≡ φ (G.pt x)) ≃⟨ funExtEquiv ⟩
    (StrictFunStr (G .fst) (H .fst) φ) ≃∎
-}

{-
  mkHGroupHom :
    ∀ (φ : ⟨ G ⟩ᵗ → ⟨ H ⟩ᵗ)
    → (pres-pt₀ : φ (hGroup.pt₀ G) ≡ hGroup.pt₀ H)
    → hGroupHom G H
  mkHGroupHom φ pres-pt₀ .fst = φ
  mkHGroupHom φ pres-pt₀ .snd = equivFun (hGroupHomStrEquiv φ) pres-pt₀

  hGroupHom≡ :
    ∀ {φ ψ : hGroupHom G H}
    → (p : φ .fst ≡ ψ .fst)
    → PathP (λ i → p i G.pt₀ ≡ H.pt₀) (hGroupHom.pres-pt₀ G H φ) (hGroupHom.pres-pt₀ G H ψ)
    → φ ≡ ψ
  hGroupHom≡ {φ} {ψ} p q = ΣPathP (p , {! !}) where
    module φ = hGroupHom G H φ
    module ψ = hGroupHom G H ψ

    -- e : PathP (λ i → StrictFunStr (fst G) (fst H) (p i)) (snd φ) (snd ψ) ≃ PathP (λ i → p i G.pt₀ ≡ H.pt₀) {! equivFun (hGroupHomStrEquiv (φ .fst)) !} {! !}
    -- e = congPathEquiv {! !}

    -- -- f : PathP (λ i → p i G.pt₀ ≡ H.pt₀) {! equivFun (hGroupHomStrEquiv (φ .fst)) !} {! !} ≃ PathP (λ i → StrictFunStr (fst G) (fst H) (p i)) (snd φ) (snd ψ)
    f : PathP (λ i → p i G.pt₀ ≡ H.pt₀) φ.pres-pt₀ ψ.pres-pt₀ ≃ PathP (λ i → StrictFunStr (fst G) (fst H) (p i)) (fst (hGroupHomStrEquiv (fst φ)) φ.pres-pt₀) (fst (hGroupHomStrEquiv (fst ψ)) ψ.pres-pt₀)
    f = congPathEquiv λ i → hGroupHomStrEquiv (p i)

    pᴰ-ext : Square (φ.pres-pt ≡$ G.center) (ψ.pres-pt ≡$ G.center) (λ i → H.pt (ST.map (p i) G.center)) (p ≡$ G.pt₀)
    pᴰ-ext = {! !}

    pᴰ : PathP (λ i → StrictFunStr (fst G) (fst H) (p i)) (snd φ) (snd ψ)
    pᴰ = funExtSquare $ G.centerElim pᴰ-ext
-}

idHGroupHom : (G : hGroup ℓ) → hGroupHom G G
idHGroupHom G .hGroupHom.fun = id _
idHGroupHom G .hGroupHom.pres-pt₀ = refl

compGroupHom : ∀ {ℓ ℓ′ ℓ″} (G : hGroup ℓ) (H : hGroup ℓ′) (K : hGroup ℓ″)
  → hGroupHom G H
  → hGroupHom H K
  → hGroupHom G K
compGroupHom G H K φ ψ .hGroupHom.fun = φ .fun ⋆ ψ .fun
compGroupHom G H K φ ψ .hGroupHom.pres-pt₀ = cong (ψ .fun) (φ .pres-pt₀) ∙ ψ .pres-pt₀

_∙ᴳ_ : ∀ {ℓ ℓ′ ℓ″} {G : hGroup ℓ} {H : hGroup ℓ′} {K : hGroup ℓ″}
  → hGroupHom G H
  → hGroupHom H K
  → hGroupHom G K
_∙ᴳ_ = compGroupHom _ _ _
