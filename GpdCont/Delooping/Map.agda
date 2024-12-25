{-# OPTIONS --lossy-unification #-}
module GpdCont.Delooping.Map where

open import GpdCont.Prelude
open import GpdCont.Group.MapConjugator using (Conjugator ; idConjugator ; compConjugator)

import GpdCont.Delooping as Delooping

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path as Path
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Foundations.Pointed using (_→∙_ ; idfun∙)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom ; compGroupHom)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

private
  variable
    ℓ : Level
    G H K : Group ℓ

  open Delooping using (𝔹)

  𝔹⋆ : {G : Group ℓ} → 𝔹 G
  𝔹⋆ = Delooping.𝔹.⋆

map : (φ : GroupHom G H) → 𝔹 G → 𝔹 H
map {G} {H} (φ , is-hom-φ) = 𝔹G.rec Delooping.isGroupoid𝔹 Delooping.⋆ φ′ φ′-comm where
  module 𝔹G = Delooping G
  module G = GroupStr (str G)
  module H = GroupStr (str H)
  
  module φ = IsGroupHom is-hom-φ

  φ′ : ⟨ G ⟩ → Delooping.⋆ ≡ Delooping.⋆
  φ′ g = Delooping.loop (φ g)

  φ′-comm : ∀ g g′ → compSquareFiller (φ′ g) (φ′ g′) (φ′ (g G.· g′))
  φ′-comm g g′ = subst (compSquareFiller _ _) (cong Delooping.loop $ sym (φ.pres· g g′)) (Delooping.loop-comp (φ g) (φ g′))

map-id : (G : Group ℓ) → map (idGroupHom {G = G}) ≡ id (𝔹 G)
map-id G = funExt (Delooping.elimSet G (λ _ → Delooping.isGroupoid𝔹 _ _) refl λ g i j → Delooping.loop g i)

map-comp : (φ : GroupHom G H) (ψ : GroupHom H K) → map (compGroupHom φ ψ) ≡ map φ ⋆ map ψ
map-comp {G} (φ , _) (ψ , _) = funExt $ Delooping.elimSet G (λ _ → Delooping.isGroupoid𝔹 _ _) refl λ g i j → Delooping.loop (ψ $ φ g) i

map∙ : (φ : GroupHom G H) → (𝔹 G , 𝔹⋆) →∙ (𝔹 H , 𝔹⋆)
map∙ φ .fst = map φ
map∙ φ .snd = refl

module _
  {φ*@(φ , _) ψ*@(ψ , _) : GroupHom G H}
  (open GroupStr (str H) using (_·_))
  (h : ⟨ H ⟩)
  (h-conj : ∀ g → (φ g · h) ≡ (h · ψ g))
  where
  private
    module BG = Delooping G
    module BH = Delooping H
    module H = GroupStr (str H)

  map-ext-⋆ : BH.⋆ ≡ BH.⋆
  map-ext-⋆ = BH.loop h

  map-ext-loop' : ∀ g → Square (BH.loop h) (BH.loop h) (BH.loop (φ g)) (BH.loop (ψ g))
  map-ext-loop' g = λ i j → hcomp {φ = ∂² i j} (sides i j) (base i j) where
    -- base : Square (BH.loop $ φ g H.· h) (BH.loop $ h H.· ψ g) refl refl
    -- base = cong BH.loop (h-conj g)

    base : Square refl refl (BH.loop $ φ g H.· h) (BH.loop $ h H.· ψ g)
    base i j = BH.loop (h-conj g j) i

    side-φg·h : Square refl (sym $ BH.loop h) (BH.loop (φ g H.· h)) (BH.loop (φ g))
    side-φg·h i k = BH.loop-comp (φ g) h (~ k) i

    side-h·ψg : Square (BH.loop h) refl (BH.loop (h H.· ψ g)) (BH.loop (ψ g))
    side-h·ψg i k = {!BH.loop-comp h (ψ g) !}


    sides : (i j k : I) → Partial (∂² i j) BH.𝔹
    sides i j k (i = i0) = {! !} -- side-φg·h j k
    sides i j k (i = i1) = {!  !}
    sides i j k (j = i0) = side-φg·h i k
    sides i j k (j = i1) = side-h·ψg i k

  map-ext-loop : ∀ g → Square (BH.loop h) (BH.loop h) (BH.loop (φ g)) (BH.loop (ψ g))
  map-ext-loop g = Path.compPath→Square $ BH.loop-∙ (φ g) h ∙∙ cong BH.loop (h-conj g) ∙∙ (sym $ BH.loop-∙ h (ψ g))

  map-ext-loop₂ : ∀ g → Square (BH.loop h) (BH.loop h) (BH.loop (φ g)) (BH.loop (ψ g))
  map-ext-loop₂ g = Path.compPath→Square $
    BH.loop (φ g) ∙ BH.loop h ≡⟨ BH.loop-∙ (φ g) h ⟩
    BH.loop (φ g H.· h)       ≡⟨ cong BH.loop (h-conj g) ⟩
    BH.loop (h H.· ψ g)       ≡⟨ sym $ BH.loop-∙ h (ψ g) ⟩
    BH.loop h ∙ BH.loop (ψ g) ∎

  map≡-ext : (x : 𝔹 G) → map φ* x ≡ map ψ* x
  map≡-ext = BG.elimSet (λ x → BH.isGroupoid𝔹 (map φ* x) (map ψ* x)) map-ext-⋆ map-ext-loop

map≡ : (φ ψ : GroupHom G H) → Conjugator φ ψ → map φ ≡ map ψ
map≡ φ ψ (h , h-conj) = funExt $ map≡-ext {φ* = φ} {ψ* = ψ} h h-conj

-- Lemmas for constructing squares in deloopings
module _ {f g : 𝔹 G → 𝔹 H}
  {p₀ : (x : 𝔹 G) → f x ≡ g x}
  {p₁ : (x : 𝔹 G) → f x ≡ g x}
  (sq⋆ : p₀ Delooping.⋆ ≡ p₁ Delooping.⋆)
  where
  private
    module 𝔹G = Delooping G
    module 𝔹H = Delooping H

  mapDepSquareExt : (x : 𝔹 G) → p₀ x ≡ p₁ x
  mapDepSquareExt = 𝔹G.elimProp isPropDepSquare sq⋆ where
    isPropDepSquare : ∀ (x : 𝔹 G) → isProp (p₀ x ≡ p₁ x)
    isPropDepSquare x = 𝔹H.isGroupoid𝔹 (f x) (g x) (p₀ x) (p₁ x)

  mapDepSquare : p₀ ≡ p₁
  mapDepSquare = funExt mapDepSquareExt


-- Computation rule for map≡ on loops
module _ {G H : Group ℓ} where
  open GroupStr (str H) using (_·_)

  map≡-loopᵝ : (φ ψ : GroupHom G H) (h : Conjugator φ ψ) (g : ⟨ G ⟩)
    → cong₂ _$_ (map≡ φ ψ h) (Delooping.loop g) ≡ Delooping.loop (h .fst · ψ .fst g)
  map≡-loopᵝ φ ψ h*@(h , h-conj) g =
    cong₂ _$_ (map≡ φ ψ h*) (Delooping.loop g)    ≡⟨ SquareDiag≡pathComp $ map-ext-loop {φ* = φ} {ψ* = ψ} h h-conj g ⟩
    Delooping.loop h ∙ Delooping.loop (ψ .fst g)  ≡⟨ Delooping.loop-∙ H h (ψ .fst g) ⟩
    Delooping.loop (h · ψ .fst g) ∎

-- Functoriality of `map≡`.
-- Identity and composition of conjugators is mapped to the reflexivity and composition of paths.
module _ {G H : Group ℓ} where
  private
    module 𝔹H = Delooping H

  map≡-id-refl : (φ : GroupHom G H) → map≡ φ φ (idConjugator φ) ≡ refl′ (map φ)
  map≡-id-refl φ = cong funExt (mapDepSquare 𝔹H.loop-1)

  map≡-comp-∙ : (φ ψ ρ : GroupHom G H)
    (h₁ : Conjugator φ ψ)
    (h₂ : Conjugator ψ ρ)
    → map≡ φ ρ (compConjugator h₁ h₂) ≡ map≡ φ ψ h₁ ∙ map≡ ψ ρ h₂
  map≡-comp-∙ _ _ _ (h₁ , _) (h₂ , _) = cong funExt $ mapDepSquare $ sym $ 𝔹H.loop-∙ h₁ h₂

module MapPathEquiv {G H : Group ℓ} where
  private
    open module H = GroupStr (str H) using (_·_)
    module 𝔹G = Delooping G
    module 𝔹H = Delooping H

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
