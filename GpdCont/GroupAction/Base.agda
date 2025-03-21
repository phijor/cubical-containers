module GpdCont.GroupAction.Base where

open import GpdCont.Prelude hiding (_▷_)
open import GpdCont.Univalence
open import GpdCont.Group.SymmetricGroup using (𝔖)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv using (funExtEquiv)
open import Cubical.Data.Sigma.Properties using (Σ-cong-iso-snd)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom ; isPropIsGroupHom ; compGroupHom)

record Action {ℓG ℓX} (G : Group ℓG) (X : hSet ℓX) : Type (ℓ-max ℓG ℓX) where
  private
    open module G = GroupStr (str G) using (_·_)

  field
    action : ⟨ G ⟩ → ⟨ 𝔖 X ⟩
    pres· : ∀ g h → action (g · h) ≡ action g ∙ₑ (action h)

  _▷_ : (g : ⟨ G ⟩) → ⟨ X ⟩ → ⟨ X ⟩
  _▷_ g = equivFun (action g)

open Action using (action ; pres·)

unquoteDecl ActionIsoΣ = declareRecordIsoΣ ActionIsoΣ (quote Action)

private
  variable
    ℓ : Level
    G H : Group ℓ
    X : hSet ℓ

_⁺_ : Action G X → ⟨ G ⟩ → ⟨ X ⟩ → ⟨ X ⟩
_⁺_ σ = _▷_ where open Action σ

ActionGroupHomIso : Iso (Action G X) (GroupHom G (𝔖 X))
ActionGroupHomIso {G} {X} =
  Action G X                                                  Iso⟨ ActionIsoΣ ⟩
  Σ[ φ ∈ (⟨ G ⟩ → ⟨ 𝔖 X ⟩) ] (∀ g h → φ (g · h) ≡ φ g ∙ₑ φ h) Iso⟨ Σ-cong-iso-snd recover-1-inv ⟩
  GroupHom G (𝔖 X) Iso∎
  where
    open module G = GroupStr (str G) using (_·_)
    module 𝔖X = GroupStr (str $ 𝔖 X)

    recover-1-inv : (φ : ⟨ G ⟩ → ⟨ 𝔖 X ⟩) → Iso (∀ g h → φ (g · h) ≡ φ g ∙ₑ φ h) (IsGroupHom (str G) φ (str $ 𝔖 X))
    recover-1-inv φ = isProp→Iso (isPropΠ2 λ g h → 𝔖X.is-set _ _) (isPropIsGroupHom _ _)
      makeIsGroupHom IsGroupHom.pres·

GroupHom→Action : GroupHom G (𝔖 X) → Action G X
GroupHom→Action = ActionGroupHomIso .Iso.inv

Action→GroupHom : Action G X → GroupHom G (𝔖 X)
Action→GroupHom = ActionGroupHomIso .Iso.fun

GroupHomPreCompAction : (φ : GroupHom G H) → Action H X → Action G X
GroupHomPreCompAction {G} {X} φ σ = GroupHom→Action φ*σ where
  φ*σ : GroupHom G (𝔖 X)
  φ*σ = compGroupHom φ $ Action→GroupHom σ

module ActionProperties {ℓX} {G : Group ℓ} {X : hSet ℓX} (σ : Action G X) where
  private
    open module G = GroupStr (str G) using (_·_)
    module σ = Action σ

  open IsGroupHom (Action→GroupHom σ .snd) using (pres1 ; presinv) public

  action-1-id : σ ⁺ G.1g ≡ id ⟨ X ⟩
  action-1-id = cong equivFun pres1

  action-comp : ∀ g h → σ ⁺ (g · h) ≡ σ ⁺ h ∘ σ ⁺ g
  action-comp g h = cong equivFun $ σ.pres· g h

  action-inv : ∀ g → (σ ⁺ G.inv g) ≡ invEq (σ.action g)
  action-inv g = cong equivFun (presinv g)

  action-cancel-left : ∀ g → (σ ⁺ G.inv g) ⋆ (σ ⁺ g) ≡ id ⟨ X ⟩
  action-cancel-left g =
      (σ ⁺ G.inv g) ⋆ (σ ⁺ g) ≡⟨ cong (_⋆ σ ⁺ g) (action-inv g) ⟩
      invEq (σ.action g) ⋆ (σ ⁺ g) ≡⟨ funExt (secEq (σ.action g)) ⟩
      id ⟨ X ⟩ ∎

  action-cancel-right : ∀ g → (σ ⁺ g) ⋆ (σ ⁺ G.inv g) ≡ id ⟨ X ⟩
  action-cancel-right g =
      (σ ⁺ g) ⋆ (σ ⁺ G.inv g) ≡⟨ cong (σ ⁺ g ⋆_) (action-inv g) ⟩
      (σ ⁺ g) ⋆ invEq (σ.action g) ≡⟨ funExt (λ x → retEq (σ.action g) x) ⟩
      id ⟨ X ⟩ ∎

  uaExtEquiv : ∀ {Y : hSet ℓ} {f₀ f₁ : ⟨ X ⟩ → ⟨ Y ⟩} (g : ⟨ G ⟩)
    → (f₀ ≡ f₁ ∘ (σ ⁺ g)) ≃ PathP (λ i → ua (σ.action g) i → ⟨ Y ⟩) f₀ f₁
  uaExtEquiv g = invEquiv funExtEquiv ∙ₑ ua→Equiv
