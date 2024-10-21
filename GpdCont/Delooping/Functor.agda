{-# OPTIONS --lossy-unification #-}
module GpdCont.Delooping.Functor where

open import GpdCont.Prelude
import GpdCont.Group.MapConjugator as MapConjugator

import GpdCont.Delooping as Delooping
open import GpdCont.Delooping.Map as Map
  using (map ; map≡ ; module MapPathEquiv)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path as Path
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Foundations.GroupoidLaws as GL using (compPathRefl)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms

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

  open MapPathEquiv {ℓ} {G} {H} using (map≡' ; map≡'Equiv ; map≡Equiv)
  open MapConjugator {ℓ} {G} {H} using (Conjugators)

  module Conjugators = Category Conjugators
  
  DeloopingPathCategory : Category _ _
  DeloopingPathCategory = DiscreteCategory ((𝔹G → 𝔹H) , isGroupoidΠ λ _ → 𝔹H.isGroupoid𝔹)

  opaque
    map≡'-id-refl : (φ : Conjugators.ob) → map≡' (φ .snd) (φ .snd) (Conjugators.id {φ}) ≡ refl′ (map (φ .snd))
    map≡'-id-refl _ = cong funExt $ Map.mapDepSquare 𝔹H.loop-1

    map≡'-comp-∙ : (φ ψ ρ : Conjugators.ob)
      (h₁ : Conjugators [ φ , ψ ])
      (h₂ : Conjugators [ ψ , ρ ])
      → (let _⋆̂_ = Conjugators._⋆_ {x = φ} {y = ψ} {z = ρ})
      → map≡' (φ .snd) (ρ .snd) (h₁ ⋆̂ h₂) ≡ map≡' (φ .snd) (ψ .snd) h₁ ∙ map≡' (ψ .snd) (ρ .snd) h₂
    map≡'-comp-∙ _ _ _ (h₁ , _) (h₂ , _) = cong funExt $ Map.mapDepSquare $ sym (𝔹H.loop-∙ h₁ h₂)

  map≡'Functor : Functor Conjugators DeloopingPathCategory
  map≡'Functor .Functor.F-ob (_ , φ) = map φ
  map≡'Functor .Functor.F-hom {x = (_ , φ)} {y = (_ , ψ)} = map≡' φ ψ
  map≡'Functor .Functor.F-id {x = φ} = map≡'-id-refl φ
  map≡'Functor .Functor.F-seq {x = φ} {y = ψ} {z = ρ} = map≡'-comp-∙ φ ψ ρ

  isFullyFaithful-map≡'Functor : Functor.isFullyFaithful map≡'Functor
  isFullyFaithful-map≡'Functor (_ , φ) (_ , ψ) = equivIsEquiv (map≡'Equiv φ ψ)

  map≡-id-refl : (φ : Conjugators.ob) → map≡ (φ .snd) (φ .snd) (Conjugators.id {φ}) ≡ refl′ (map (φ .snd))
  map≡-id-refl φ = cong funExt (Map.mapDepSquare 𝔹H.loop-1)

  map≡-comp-∙ : (φ ψ ρ : Conjugators.ob)
    (h₁ : Conjugators [ φ , ψ ])
    (h₂ : Conjugators [ ψ , ρ ])
    → (let _⋆̂_ = Conjugators._⋆_ {x = φ} {y = ψ} {z = ρ})
    → map≡ (φ .snd) (ρ .snd) (h₁ ⋆̂ h₂) ≡ map≡ (φ .snd) (ψ .snd) h₁ ∙ map≡ (ψ .snd) (ρ .snd) h₂
  map≡-comp-∙ _ _ _ (h₁ , _) (h₂ , _) = cong funExt (Map.mapDepSquare (sym (𝔹H.loop-∙ h₁ h₂)))

  map≡Functor : Functor Conjugators DeloopingPathCategory
  map≡Functor .Functor.F-ob (_ , φ) = map φ
  map≡Functor .Functor.F-hom {x = (_ , φ)} {y = (_ , ψ)} = map≡ φ ψ
  map≡Functor .Functor.F-id {x = φ} = map≡-id-refl φ
  map≡Functor .Functor.F-seq {x = φ} {y = ψ} {z = ρ} = map≡-comp-∙ φ ψ ρ

  isFullyFaithful-map≡Functor : Functor.isFullyFaithful map≡Functor
  isFullyFaithful-map≡Functor (_ , φ) (_ , ψ) = equivIsEquiv (map≡Equiv φ ψ)

module Global {ℓ : Level} where
  open import GpdCont.WildCat.HomotopyCategory as HomotopyCategory using (ho)

  open import GpdCont.Groups.Base renaming (Group to ConcreteGroup ; GroupStr to ConcreteGroupStr)
  open import GpdCont.Groups.Homomorphism using () renaming (GroupHom to ConcreteGroupHom ; GroupHom≡ to ConcreteGroupHom≡)
  open import GpdCont.Groups.Category using () renaming (GroupCategory to ConcreteGroupCategory)

  open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom ; compGroupHom)

  open import Cubical.Categories.Category.Base using (Category ; _^op ; _[_,_] ; seq')
  open import Cubical.Categories.Functor.Base using (Functor)
  open import Cubical.Categories.Instances.Groups using (GroupCategory)
  open import Cubical.Categories.Instances.Sets using (SET)
  open import Cubical.WildCat.Base renaming (_[_,_] to _[_,_]ʷ) hiding (concatMor)

  private
    hoGrp = ho (ConcreteGroupCategory ℓ)

  module DeloopingFunctor where
    open HomotopyCategory.Notation (ConcreteGroupCategory ℓ)
      using (hoHom ; trunc-hom)

    ob : Group ℓ → ConcreteGroup ℓ
    ob G = 𝔹G , 𝔹G-str where
      open module 𝔹G = Delooping ⟨ G ⟩ (str G) renaming (𝔹 to 𝔹G)

      𝔹G-str : ConcreteGroupStr 𝔹G
      𝔹G-str .ConcreteGroupStr.is-connected = isConnectedDelooping
      𝔹G-str .ConcreteGroupStr.is-groupoid = Delooping.isGroupoid𝔹
      𝔹G-str .ConcreteGroupStr.pt = Delooping.⋆

    hom : {G H : Group ℓ} (φ : GroupHom G H) → hoHom (ob G) (ob H)
    hom {G} {H} φ = trunc-hom 𝔹φ where
      open ConcreteGroupHom
      𝔹φ : ConcreteGroupHom (ob G) (ob H)
      𝔹φ .pt-map = Map.map∙ φ

    hom-id : {G : Group ℓ} → hom (idGroupHom {G = G}) ≡ trunc-hom (WildCat.id (ConcreteGroupCategory ℓ))
    hom-id {G} = cong trunc-hom $ ConcreteGroupHom≡ (Map.map-id G) refl

    hom-seq : {G H K : Group ℓ} (φ : GroupHom G H) (ψ : GroupHom H K)
      → hom (compGroupHom φ ψ) ≡ (hom φ ⋆⟨ hoGrp ⟩ hom ψ)
    hom-seq φ ψ = cong trunc-hom (ConcreteGroupHom≡ (Map.map-comp φ ψ) compPathRefl)

  DeloopingFunctor : Functor (GroupCategory {ℓ}) hoGrp
  DeloopingFunctor .Functor.F-ob = DeloopingFunctor.ob
  DeloopingFunctor .Functor.F-hom = DeloopingFunctor.hom
  DeloopingFunctor .Functor.F-id = DeloopingFunctor.hom-id
  DeloopingFunctor .Functor.F-seq = DeloopingFunctor.hom-seq
