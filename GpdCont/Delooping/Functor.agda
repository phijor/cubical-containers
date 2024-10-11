module GpdCont.Delooping.Functor where

open import GpdCont.Prelude

import GpdCont.Delooping as Delooping
open import GpdCont.Delooping.Map using (map ; map≡ ; module MapPathEquiv ; mapDepSquare)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path as Path
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
-- open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.StructureOver

module Local {ℓ} {G H : Group ℓ} where
  private
    open module H = GroupStr (str H) using (_·_)

    𝔹G = Delooping.𝔹 ⟨ G ⟩ (str G)
    𝔹H = Delooping.𝔹 ⟨ H ⟩ (str H)

    module 𝔹G = Delooping ⟨ G ⟩ (str G)
    module 𝔹H = Delooping ⟨ H ⟩ (str H)

    variable
      φ ψ : GroupHom G H

  open MapPathEquiv {ℓ} {G} {H}

  Conjugators : Category ℓ ℓ
  Conjugators = ∫C {C = B[H]} (StructureOver→Catᴰ ConjugatorStr) where
    B[H] : Category _ _
    B[H] .Category.ob = Unit
    B[H] .Category.Hom[_,_] _ _ = ⟨ H ⟩
    B[H] .Category.id = H.1g
    B[H] .Category._⋆_ = H._·_
    B[H] .Category.⋆IdL = H.·IdL
    B[H] .Category.⋆IdR = H.·IdR
    B[H] .Category.⋆Assoc f g h = sym $ H.·Assoc f g h
    B[H] .Category.isSetHom = H.is-set

    ConjugatorStr : StructureOver B[H] _ _
    ConjugatorStr .StructureOver.ob[_] = const (GroupHom G H)
    ConjugatorStr .StructureOver.Hom[_][_,_] h (φ , _) (ψ , _) = ∀ g → φ g · h ≡ h · ψ g
    ConjugatorStr .StructureOver.idᴰ g = H.·IdR _ ∙ sym (H.·IdL _)
    ConjugatorStr .StructureOver._⋆ᴰ_ {f = h₁} {g = h₂} {xᴰ = (φ , _)} {yᴰ = (ψ , _)} {zᴰ = (ρ , _)} conj-h₁ conj-h₂ g =
      φ g · (h₁ · h₂) ≡⟨ H.·Assoc _ _ _ ⟩
      (φ g · h₁) · h₂ ≡⟨ cong (_· h₂) (conj-h₁ g) ⟩
      (h₁ · ψ g) · h₂ ≡⟨ sym $ H.·Assoc _ _ _ ⟩
      h₁ · (ψ g · h₂) ≡⟨ cong (h₁ ·_) (conj-h₂ g) ⟩
      h₁ · (h₂ · ρ g) ≡⟨ H.·Assoc _ _ _ ⟩
      (h₁ · h₂) · ρ g ∎
    ConjugatorStr .StructureOver.isPropHomᴰ = isPropΠ λ g → H.is-set _ _

  module Conjugators = Category Conjugators
  
  DeloopingPathCategory : Category _ _
  DeloopingPathCategory = DiscreteCategory ((𝔹G → 𝔹H) , isGroupoidΠ λ _ → 𝔹H.isGroupoid𝔹)

  opaque
    map≡'-id-refl : (φ : Conjugators.ob) → map≡' (φ .snd) (φ .snd) (Conjugators.id {φ}) ≡ refl′ (map (φ .snd))
    map≡'-id-refl _ = cong funExt $ mapDepSquare 𝔹H.loop-1

    map≡'-comp-∙ : (φ ψ ρ : Conjugators.ob)
      (h₁ : Conjugators [ φ , ψ ])
      (h₂ : Conjugators [ ψ , ρ ])
      → (let _⋆̂_ = Conjugators._⋆_ {x = φ} {y = ψ} {z = ρ})
      → map≡' (φ .snd) (ρ .snd) (h₁ ⋆̂ h₂) ≡ map≡' (φ .snd) (ψ .snd) h₁ ∙ map≡' (ψ .snd) (ρ .snd) h₂
    map≡'-comp-∙ _ _ _ (h₁ , _) (h₂ , _) = cong funExt $ mapDepSquare $ sym (𝔹H.loop-∙ h₁ h₂)

  map≡'Functor : Functor Conjugators DeloopingPathCategory
  map≡'Functor .Functor.F-ob (_ , φ) = map φ
  map≡'Functor .Functor.F-hom {x = (_ , φ)} {y = (_ , ψ)} = map≡' φ ψ
  map≡'Functor .Functor.F-id {x = φ} = map≡'-id-refl φ
  map≡'Functor .Functor.F-seq {x = φ} {y = ψ} {z = ρ} = map≡'-comp-∙ φ ψ ρ

  isFullyFaithful-map≡'Functor : Functor.isFullyFaithful map≡'Functor
  isFullyFaithful-map≡'Functor (_ , φ) (_ , ψ) = equivIsEquiv (map≡'Equiv φ ψ)

  map≡-id-refl : (φ : Conjugators.ob) → map≡ (φ .snd) (φ .snd) (Conjugators.id {φ}) ≡ refl′ (map (φ .snd))
  map≡-id-refl φ = cong funExt (mapDepSquare 𝔹H.loop-1)

  map≡-comp-∙ : (φ ψ ρ : Conjugators.ob)
    (h₁ : Conjugators [ φ , ψ ])
    (h₂ : Conjugators [ ψ , ρ ])
    → (let _⋆̂_ = Conjugators._⋆_ {x = φ} {y = ψ} {z = ρ})
    → map≡ (φ .snd) (ρ .snd) (h₁ ⋆̂ h₂) ≡ map≡ (φ .snd) (ψ .snd) h₁ ∙ map≡ (ψ .snd) (ρ .snd) h₂
  map≡-comp-∙ _ _ _ (h₁ , _) (h₂ , _) = cong funExt (mapDepSquare (sym (𝔹H.loop-∙ h₁ h₂)))

{-
  map≡Functor : Functor Conjugators DeloopingPathCategory
  map≡Functor .Functor.F-ob (_ , φ) = map φ
  map≡Functor .Functor.F-hom {x = (_ , φ)} {y = (_ , ψ)} = map≡ φ ψ
  map≡Functor .Functor.F-id {x = φ} = map≡-id-refl φ
  map≡Functor .Functor.F-seq {x = φ} {y = ψ} {z = ρ} = map≡-comp-∙ φ ψ ρ

  isFullyFaithful-map≡Functor : Functor.isFullyFaithful map≡Functor
  isFullyFaithful-map≡Functor (_ , φ) (_ , ψ) = equivIsEquiv (map≡Equiv φ ψ)
-}
