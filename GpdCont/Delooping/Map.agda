module GpdCont.Delooping.Map where

open import GpdCont.Prelude

import GpdCont.Delooping as Delooping

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path as Path
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

private
  variable
    ℓ : Level
    G H : Group ℓ

  𝔹 : (G : Group ℓ) → Type ℓ
  𝔹 = uncurry Delooping.𝔹

map : (φ : GroupHom G H) → 𝔹 G → 𝔹 H
map {G} {H} (φ , is-hom-φ) = Delooping.rec ⟨ G ⟩ (str G) Delooping.isGroupoid𝔹 Delooping.⋆ φ′ φ′-comm where
  module G = GroupStr (str G)
  module H = GroupStr (str H)
  
  module φ = IsGroupHom is-hom-φ

  φ′ : ⟨ G ⟩ → Delooping.⋆ ≡ Delooping.⋆
  φ′ g = Delooping.loop (φ g)

  φ′-comm : ∀ g g′ → compSquareFiller (φ′ g) (φ′ g′) (φ′ (g G.· g′))
  φ′-comm g g′ = subst (compSquareFiller _ _) (cong Delooping.loop $ sym (φ.pres· g g′)) (Delooping.loop-comp (φ g) (φ g′))

map-id : (G : Group ℓ) → map (idGroupHom {G = G}) ≡ id (𝔹 G)
map-id G = funExt (Delooping.elimSet ⟨ G ⟩  (str G) (λ _ → Delooping.isGroupoid𝔹 _ _) refl λ g i j → Delooping.loop g i)

module _
  {φ*@(φ , _) ψ*@(ψ , _) : GroupHom G H}
  (open GroupStr (str H) using (_·_))
  (h : ⟨ H ⟩)
  (h-conj : ∀ g → (φ g · h) ≡ (h · ψ g))
  where
  private
    module BG = Delooping ⟨ G ⟩ (str G)
    module BH = Delooping ⟨ H ⟩ (str H)
    module H = GroupStr (str H)

    map-ext-⋆ : BH.⋆ ≡ BH.⋆
    map-ext-⋆ = BH.loop h

    map-ext-loop : ∀ g → Square (BH.loop h) (BH.loop h) (BH.loop (φ g)) (BH.loop (ψ g))
    map-ext-loop g = Path.compPath→Square $
      BH.loop (φ g) ∙ BH.loop h ≡⟨ BH.loop-∙ (φ g) h ⟩
      BH.loop (φ g H.· h)       ≡⟨ cong BH.loop (h-conj g) ⟩
      BH.loop (h H.· ψ g)       ≡⟨ sym $ BH.loop-∙ h (ψ g) ⟩
      BH.loop h ∙ BH.loop (ψ g) ∎

  map≡-ext : (x : 𝔹 G) → map φ* x ≡ map ψ* x
  map≡-ext = BG.elimSet (λ x → BH.isGroupoid𝔹 (map φ* x) (map ψ* x)) map-ext-⋆ map-ext-loop

Conjugator : (φ ψ : GroupHom G H) → Type _
Conjugator {H} (φ , _) (ψ , _) = Σ[ h ∈ ⟨ H ⟩ ] ∀ g → φ g · h ≡ h · ψ g where
  open GroupStr (str H) using (_·_)

map≡ : (φ ψ : GroupHom G H) → Conjugator φ ψ → map φ ≡ map ψ
map≡ φ ψ (h , h-conj) = funExt $ map≡-ext {φ* = φ} {ψ* = ψ} h h-conj

module _ {f g : 𝔹 G → 𝔹 H}
  {p₀ : (x : 𝔹 G) → f x ≡ g x}
  {p₁ : (x : 𝔹 G) → f x ≡ g x}
  (sq⋆ : p₀ Delooping.⋆ ≡ p₁ Delooping.⋆)
  where
  private
    module 𝔹G = Delooping ⟨ G ⟩ (str G)
    module 𝔹H = Delooping ⟨ H ⟩ (str H)

  mapDepSquareExt : (x : 𝔹 G) → p₀ x ≡ p₁ x
  mapDepSquareExt = 𝔹G.elimProp isPropDepSquare sq⋆ where
    isPropDepSquare : ∀ (x : 𝔹 G) → isProp (p₀ x ≡ p₁ x)
    isPropDepSquare x = 𝔹H.isGroupoid𝔹 (f x) (g x) (p₀ x) (p₁ x)

  mapDepSquare : p₀ ≡ p₁
  mapDepSquare = funExt mapDepSquareExt

module MapPathEquiv {G H : Group ℓ} where
  private
    open module H = GroupStr (str H) using (_·_)
    module 𝔹G = Delooping ⟨ G ⟩ (str G)
    module 𝔹H = Delooping ⟨ H ⟩ (str H)

  map≡'Equiv : (φ ψ : GroupHom G H) → (Conjugator φ ψ) ≃ (map φ ≡ map ψ)
  map≡'Equiv φ*@(φ , _) ψ*@(ψ , _) =
    (Σ[ h ∈ ⟨ H ⟩ ] ∀ g → φ g · h ≡ h · ψ g)
      ≃⟨ Σ-cong-equiv (invEquiv 𝔹H.ΩDelooping≃) (equivΠCod ∘ lemma) ⟩
    (Σ[ l ∈ 𝔹H.⋆ ≡ 𝔹H.⋆ ] ∀ g → Square l l (𝔹H.loop (φ g)) (𝔹H.loop (ψ g)))
      ≃⟨ 𝔹G.elimSetEquiv {B = λ x → map φ* x ≡ map ψ* x} (λ x → 𝔹H.isGroupoid𝔹 _ _) ⟩
    (∀ (x : 𝔹 G) → map φ* x ≡ map ψ* x)
      ≃⟨ funExtEquiv ⟩
    (map φ* ≡ map ψ*) ≃∎ where

    lemma : ∀ h g → ((φ g) · h ≡ h · (ψ g)) ≃ Square (𝔹H.loop h) (𝔹H.loop h) (𝔹H.loop (φ g)) (𝔹H.loop (ψ g))
    lemma h g =
      ((φ g) · h ≡ h · (ψ g)) ≃⟨ congEquiv $ invEquiv 𝔹H.ΩDelooping≃ ⟩
      𝔹H.loop ((φ g) · h) ≡ 𝔹H.loop (h · (ψ g)) ≃⟨ pathToEquiv $ sym $ cong₂ _≡_ (𝔹H.loop-∙ _ _) (𝔹H.loop-∙ _ _) ⟩
      𝔹H.loop (φ g) ∙ (𝔹H.loop h) ≡ 𝔹H.loop h ∙ 𝔹H.loop (ψ g) ≃⟨ compPath≃Square ⟩
      Square (𝔹H.loop h) (𝔹H.loop h) (𝔹H.loop (φ g)) (𝔹H.loop (ψ g)) ≃∎

  map≡' : (φ ψ : GroupHom G H) → (Σ[ h ∈ ⟨ H ⟩ ] ∀ g → φ .fst g · h ≡ h · ψ .fst g) → (map φ ≡ map ψ)
  map≡' φ ψ = equivFun (map≡'Equiv φ ψ)

  map≡'-map≡-path : (φ ψ : GroupHom G H) → map≡' φ ψ ≡ map≡ φ ψ
  map≡'-map≡-path φ ψ = funExt λ { (h , h-conj) → cong funExt $ (mapDepSquare $ refl′ (𝔹H.𝔹.loop h)) }

  isEquiv-map≡ : ∀ (φ ψ : GroupHom G H) → isEquiv (map≡ φ ψ)
  isEquiv-map≡ φ ψ = subst isEquiv (map≡'-map≡-path φ ψ) (equivIsEquiv (map≡'Equiv φ ψ))

  map≡Equiv : (φ ψ : GroupHom G H) → (Conjugator φ ψ) ≃ (map φ ≡ map ψ)
  map≡Equiv φ ψ .fst = map≡ φ ψ
  map≡Equiv φ ψ .snd = isEquiv-map≡ φ ψ

open MapPathEquiv using (map≡Equiv) public
