module GpdCont.HomotopyGroup.Morphism where

open import GpdCont.Prelude

open import GpdCont.Equiv
open import GpdCont.HomotopyGroup.Base
open import GpdCont.StrictGroupoid.Morphism

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path using (compPathrEquiv ; congPathEquiv)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)

private
  variable
    ℓ ℓ′ : Level

hGroupHom : (G : hGroup ℓ) (H : hGroup ℓ′) → Type _
hGroupHom (G , _) (H , _) = StrictFun G H

module hGroupHom {ℓ} {ℓ′} (G : hGroup ℓ) (H : hGroup ℓ′) (φ : hGroupHom G H) where
  private
    module G = hGroup G
    module H = hGroup H

  open Σ φ public renaming (fst to fun ; snd to pres-pt)

  pres-pt₀ : fun G.pt₀ ≡ H.pt₀
  pres-pt₀ = sym (pres-pt ≡$ G.center) ∙ cong H.pt (isContr→isProp H.is-connected (ST.map fun G.center) H.center)

module _ {ℓ} {ℓ′} (G : hGroup ℓ) (H : hGroup ℓ′) where
  private
    module G = hGroup G
    module H = hGroup H

  isSetHGroupHom : isSet (hGroupHom G H)
  isSetHGroupHom = isSetStrictFun (G .fst) (H .fst)

  hGroupHomStrEquiv : (φ : ⟨ G ⟩ᵗ → ⟨ H ⟩ᵗ) → (φ G.pt₀ ≡ H.pt₀) ≃ (StrictFunStr (G .fst) (H .fst) φ)
  hGroupHomStrEquiv φ =
    (φ G.pt₀ ≡ H.pt₀) ≃⟨ compPathrEquiv $ cong H.pt (isContr→isProp H.is-connected H.center (ST.map φ G.center)) ⟩
    (φ G.pt₀ ≡ H.pt (ST.map φ G.center)) ≃⟨ symEquiv ⟩
    (H.pt (ST.map φ G.center) ≡ φ G.pt₀) ≃⟨ G.centerElimEquiv ⟩
    ((x : G.Tr) → H.pt (ST.map φ x) ≡ φ (G.pt x)) ≃⟨ funExtEquiv ⟩
    (StrictFunStr (G .fst) (H .fst) φ) ≃∎

  hGroupHomEquiv : (Σ[ φ ∈ (⟨ G ⟩ᵗ → ⟨ H ⟩ᵗ) ] φ G.pt₀ ≡ H.pt₀) ≃ (hGroupHom G H)
  hGroupHomEquiv = Σ-cong-equiv-snd hGroupHomStrEquiv

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

