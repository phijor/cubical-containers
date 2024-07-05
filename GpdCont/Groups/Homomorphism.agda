module GpdCont.Groups.Homomorphism where

open import GpdCont.Prelude hiding (id ; comp)
open import GpdCont.Groups.Base

open import Cubical.Foundations.Pointed using (_→∙_ ; idfun∙)
open import Cubical.Foundations.GroupoidLaws as GL using ()

record GroupHom {ℓ} (G H : Group ℓ) : Type ℓ where
  constructor mkGroupHom
  field
    pt-map : ⟨ G ⟩∙ →∙ ⟨ H ⟩∙

private
  variable
    ℓ : Level
    G H K : Group ℓ

open GroupHom

⟪_⟫ : GroupHom G H → ⟨ G ⟩ → ⟨ H ⟩
⟪ φ ⟫ = φ .pt-map .fst

⟪_⟫-pres-pt : (φ : GroupHom G H) → ⟪ φ ⟫ (G ∙) ≡ H ∙
⟪_⟫-pres-pt φ = φ .pt-map .snd

GroupHom≡ : {φ ψ : GroupHom {ℓ} G H}
  → (p : ⟪ φ ⟫ ≡ ⟪ ψ ⟫)
  → PathP (λ i → p i (G ∙) ≡ H ∙) ⟪ φ ⟫-pres-pt ⟪ ψ ⟫-pres-pt
  → φ ≡ ψ
GroupHom≡ p q i .pt-map .fst = p i
GroupHom≡ p q i .pt-map .snd = q i

id : (G : Group ℓ) → GroupHom G G
id G .pt-map = idfun∙ ⟨ G ⟩∙

comp : (φ : GroupHom G H) (ψ : GroupHom H K) → GroupHom G K
comp φ ψ .pt-map .fst = ⟪ φ ⟫ ⋆ ⟪ ψ ⟫
comp φ ψ .pt-map .snd = cong ⟪ ψ ⟫ ⟪ φ ⟫-pres-pt ∙ ⟪ ψ ⟫-pres-pt

compIdL : (ψ : GroupHom G H) → comp (id G) ψ ≡ ψ
compIdL {G} ψ = GroupHom≡ refl pres-pt-path where
  pres-pt-path : cong ⟪ ψ ⟫ refl ∙ ⟪ ψ ⟫-pres-pt ≡ ⟪ ψ ⟫-pres-pt
  pres-pt-path = sym $ GL.lUnit ⟪ ψ ⟫-pres-pt

compIdR : (φ : GroupHom G H) → comp φ (id H) ≡ φ
compIdR {H} φ = GroupHom≡ refl pres-pt-path where
  pres-pt-path : cong ⟪ id H ⟫ ⟪ φ ⟫-pres-pt ∙ refl ≡ ⟪ φ ⟫-pres-pt
  pres-pt-path = sym $ GL.rUnit $ ⟪ φ ⟫-pres-pt
