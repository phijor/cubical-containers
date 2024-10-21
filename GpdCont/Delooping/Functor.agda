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
    map≡'-id-refl : (φ : Conjugators.ob) → map≡' φ φ (Conjugators.id {φ}) ≡ refl′ (map φ)
    map≡'-id-refl _ = cong funExt $ Map.mapDepSquare 𝔹H.loop-1

    map≡'-comp-∙ : (φ ψ ρ : Conjugators.ob)
      (h₁ : Conjugators [ φ , ψ ])
      (h₂ : Conjugators [ ψ , ρ ])
      → (let _⋆̂_ = Conjugators._⋆_ {x = φ} {y = ψ} {z = ρ})
      → map≡' φ ρ (h₁ ⋆̂ h₂) ≡ map≡' φ ψ h₁ ∙ map≡' ψ ρ h₂
    map≡'-comp-∙ _ _ _ (h₁ , _) (h₂ , _) = cong funExt $ Map.mapDepSquare $ sym (𝔹H.loop-∙ h₁ h₂)

  map≡'Functor : Functor Conjugators DeloopingPathCategory
  map≡'Functor .Functor.F-ob φ = map φ
  map≡'Functor .Functor.F-hom {x = φ} {y = ψ} = map≡' φ ψ
  map≡'Functor .Functor.F-id {x = φ} = map≡'-id-refl φ
  map≡'Functor .Functor.F-seq {x = φ} {y = ψ} {z = ρ} = map≡'-comp-∙ φ ψ ρ

  isFullyFaithful-map≡'Functor : Functor.isFullyFaithful map≡'Functor
  isFullyFaithful-map≡'Functor φ ψ = equivIsEquiv (map≡'Equiv φ ψ)

  map≡-id-refl : (φ : Conjugators.ob) → map≡ φ φ (Conjugators.id {φ}) ≡ refl′ (map φ)
  map≡-id-refl φ = cong funExt (Map.mapDepSquare 𝔹H.loop-1)

  map≡-comp-∙ : (φ ψ ρ : Conjugators.ob)
    (h₁ : Conjugators [ φ , ψ ])
    (h₂ : Conjugators [ ψ , ρ ])
    → (let _⋆̂_ = Conjugators._⋆_ {x = φ} {y = ψ} {z = ρ})
    → map≡ φ ρ (h₁ ⋆̂ h₂) ≡ map≡ φ ψ h₁ ∙ map≡ ψ ρ h₂
  map≡-comp-∙ _ _ _ (h₁ , _) (h₂ , _) = cong funExt (Map.mapDepSquare (sym (𝔹H.loop-∙ h₁ h₂)))

  map≡Functor : Functor Conjugators DeloopingPathCategory
  map≡Functor .Functor.F-ob φ = map φ
  map≡Functor .Functor.F-hom {x = φ} {y = ψ} = map≡ φ ψ
  map≡Functor .Functor.F-id {x = φ} = map≡-id-refl φ
  map≡Functor .Functor.F-seq {x = φ} {y = ψ} {z = ρ} = map≡-comp-∙ φ ψ ρ

  isFullyFaithful-map≡Functor : Functor.isFullyFaithful map≡Functor
  isFullyFaithful-map≡Functor φ ψ = equivIsEquiv (map≡Equiv φ ψ)

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

module TwoFunc (ℓ : Level) where
  open import GpdCont.TwoCategory.Base
  open import GpdCont.TwoCategory.Pseudofunctor
  open import GpdCont.Group.MapConjugator using (Conjugator ; idConjugator ; compConjugator)
  open import GpdCont.Group.TwoCategory using (TwoGroup)
  open import GpdCont.TwoCategory.HomotopyGroupoid using (hGpdCat)

  open import Cubical.Algebra.Group.MorphismProperties

  private
    variable
      G H K L : Group ℓ
      φ ψ ρ : GroupHom G H

    module TwoGroup = TwoCategory (TwoGroup ℓ)
    module hGpdCat = TwoCategory (hGpdCat ℓ)

    𝔹-ob : Group ℓ → hGroupoid ℓ
    𝔹-ob (G , G-str) = Delooping.𝔹 G G-str , Delooping.isGroupoid𝔹

    𝔹-hom : {G H : Group ℓ} → GroupHom G H → ⟨ 𝔹-ob G ⟩ → ⟨ 𝔹-ob H ⟩
    𝔹-hom φ = Map.map φ

    𝔹-rel : {G H : Group ℓ} {φ ψ : GroupHom G H} → Conjugator φ ψ → 𝔹-hom φ ≡ 𝔹-hom ψ
    𝔹-rel {φ} {ψ} = map≡ φ ψ

    𝔹-rel-id : 𝔹-rel (idConjugator φ) ≡ refl
    𝔹-rel-id {φ} = Local.map≡-id-refl φ

    𝔹-rel-trans : (h₁ : Conjugator φ ψ) (h₂ : Conjugator ψ ρ) → 𝔹-rel (compConjugator h₁ h₂) ≡ 𝔹-rel h₁ ∙ 𝔹-rel h₂
    𝔹-rel-trans {φ} {ψ} {ρ} = Local.map≡-comp-∙ φ ψ ρ

    𝔹-trans-lax : (φ : GroupHom G H) (ψ : GroupHom H K) → (𝔹-hom φ hGpdCat.∙₁ 𝔹-hom ψ) ≡ 𝔹-hom (compGroupHom φ ψ)
    𝔹-trans-lax {G} {H} {K} φ ψ = funExt (Delooping.elimSet ⟨ G ⟩ (str G) isSetMotive refl λ g i j → 𝔹K.loop (compGroupHom φ ψ .fst g) i) where
      module 𝔹G = Delooping.𝔹 ⟨ G ⟩ (str G)
      module 𝔹K = Delooping.𝔹 ⟨ K ⟩ (str K)

      isSetMotive : (x : Delooping.𝔹 ⟨ G ⟩ (str G)) → isSet ((𝔹-hom ψ $ 𝔹-hom φ x) ≡ (𝔹-hom (compGroupHom φ ψ) x))
      isSetMotive x = 𝔹K.isGroupoid𝔹 _ _

    𝔹-trans-lax-natural : {φ₁ φ₂ : GroupHom G H} {ψ₁ ψ₂ : GroupHom H K}
      → (h : Conjugator φ₁ φ₂)
      → (k : Conjugator ψ₁ ψ₂)
      → ((𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ∙ 𝔹-trans-lax φ₂ ψ₂) ≡ (𝔹-trans-lax φ₁ ψ₁ ∙ 𝔹-rel (h TwoGroup.∙ₕ k))
    𝔹-trans-lax-natural {G} {H} {K} {φ₁} {φ₂} {ψ₁} {ψ₂} h k = funExtSquare _ _ _ _ lax where
      module K = GroupStr (str K)
      𝔹G = Delooping.𝔹 ⟨ G ⟩ (str G)
      𝔹H = Delooping.𝔹 ⟨ H ⟩ (str H)
      𝔹K = Delooping.𝔹 ⟨ K ⟩ (str K)
      module 𝔹G = Delooping ⟨ G ⟩ (str G)
      module 𝔹H = Delooping ⟨ H ⟩ (str H)
      module 𝔹K = Delooping ⟨ K ⟩ (str K)

      ap⋆ : {f g : 𝔹G → 𝔹K} → (p : f ≡ g) → f 𝔹G.⋆ ≡ g 𝔹G.⋆
      ap⋆ = cong (λ f → f 𝔹G.⋆)

      lax⋆ : ap⋆ (((𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ∙ 𝔹-trans-lax φ₂ ψ₂)) ≡ ap⋆ (𝔹-trans-lax φ₁ ψ₁ ∙ 𝔹-rel (h TwoGroup.∙ₕ k))
      lax⋆ =
        ap⋆ (((𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ∙ 𝔹-trans-lax φ₂ ψ₂)) ≡⟨ GL.cong-∙ (λ f → f 𝔹G.⋆) (𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) (𝔹-trans-lax φ₂ ψ₂) ⟩
        ap⋆ (𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ∙ ap⋆ (𝔹-trans-lax φ₂ ψ₂) ≡⟨⟩
        ap⋆ (𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ∙ refl ≡⟨ sym $ GL.rUnit _ ⟩

        ap⋆ (𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ≡⟨ Map.map≡-loopᵝ ψ₁ ψ₂ k (h .fst) ⟩
        𝔹K.loop ((h TwoGroup.∙ₕ k) .fst) ≡⟨⟩

        ap⋆ (𝔹-rel (h TwoGroup.∙ₕ k)) ≡⟨ GL.lUnit _ ⟩
        refl ∙ ap⋆ (𝔹-rel (h TwoGroup.∙ₕ k)) ≡⟨⟩
        ap⋆ (𝔹-trans-lax φ₁ ψ₁) ∙ ap⋆ (𝔹-rel (h TwoGroup.∙ₕ k)) ≡⟨ sym $ GL.cong-∙ (λ f → f 𝔹G.⋆) (𝔹-trans-lax φ₁ ψ₁) (𝔹-rel (h TwoGroup.∙ₕ k)) ⟩
        ap⋆ (𝔹-trans-lax φ₁ ψ₁ ∙ 𝔹-rel (h TwoGroup.∙ₕ k)) ∎

      lax : (x : 𝔹G) → (((𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ∙ 𝔹-trans-lax φ₂ ψ₂) ≡$S x) ≡ (𝔹-trans-lax φ₁ ψ₁ ∙ 𝔹-rel (h TwoGroup.∙ₕ k) ≡$S x)
      lax = 𝔹G.elimProp (λ x → 𝔹K.isGroupoid𝔹 _ _ _ _) lax⋆

    𝔹-id-lax : (G : Group ℓ) → id ⟨ 𝔹-ob G ⟩ ≡ 𝔹-hom (idGroupHom {G = G})
    𝔹-id-lax G = sym (Map.map-id G)

    𝔹-assoc : (φ : GroupHom G H) (ψ : GroupHom H K) (ρ : GroupHom K L)
      → Square
        ((𝔹-trans-lax φ ψ hGpdCat.∙ₕ refl′ (𝔹-hom ρ)) ∙ 𝔹-trans-lax (φ TwoGroup.∙₁ ψ) ρ)
        ((refl′ (𝔹-hom φ) hGpdCat.∙ₕ 𝔹-trans-lax ψ ρ) ∙ 𝔹-trans-lax φ (ψ TwoGroup.∙₁ ρ))
        (refl′ ((𝔹-hom φ hGpdCat.∙₁ 𝔹-hom ψ) hGpdCat.∙₁ 𝔹-hom ρ))
        (cong 𝔹-hom (TwoGroup.comp-hom-assoc φ ψ ρ))
    𝔹-assoc {G} {H} {L} φ ψ ρ = funExtSquare _ _ _ _ assoc-ext where
      𝔹G = Delooping.𝔹 ⟨ G ⟩ (str G)
      𝔹L = Delooping.𝔹 ⟨ L ⟩ (str L)
      module 𝔹G = Delooping ⟨ G ⟩ (str G)
      module 𝔹L = Delooping ⟨ L ⟩ (str L)

      open 𝔹G using (cong⋆ ; cong⋆-∙)

      assoc-ext : (x : 𝔹G) → Square
        ((𝔹-trans-lax φ ψ hGpdCat.∙ₕ refl′ (𝔹-hom ρ)) ∙ 𝔹-trans-lax (φ TwoGroup.∙₁ ψ) ρ ≡$ x)
        (((refl′ (𝔹-hom φ) hGpdCat.∙ₕ 𝔹-trans-lax ψ ρ) ∙ 𝔹-trans-lax φ (ψ TwoGroup.∙₁ ρ)) ≡$ x)
        refl
        (λ i → 𝔹-hom (TwoGroup.comp-hom-assoc φ ψ ρ i) x)
      assoc-ext = 𝔹G.elimProp (λ x → 𝔹L.isPropDeloopingSquare) $
        let
          p = (𝔹-trans-lax φ ψ hGpdCat.∙ₕ refl′ (𝔹-hom ρ))
          q = (𝔹-trans-lax (φ TwoGroup.∙₁ ψ) ρ)
          r = (refl′ (𝔹-hom φ) hGpdCat.∙ₕ 𝔹-trans-lax ψ ρ)
          s = (𝔹-trans-lax φ (ψ TwoGroup.∙₁ ρ))
        in
        (cong⋆ $ p ∙ q)     ≡⟨ cong⋆-∙ p q ⟩
        (cong⋆ p ∙ cong⋆ q) ≡⟨⟩
        (refl ∙ refl)       ≡⟨ sym $ cong⋆-∙ r s ⟩
        (cong⋆ $ r ∙ s)     ∎

    𝔹-unit-left : (φ : GroupHom G H) → Square
      ((𝔹-id-lax G hGpdCat.∙ₕ refl′ (𝔹-hom φ)) hGpdCat.∙ᵥ 𝔹-trans-lax idGroupHom φ)
      (refl′ (𝔹-hom φ))
      (hGpdCat.comp-hom-unit-left (𝔹-hom φ))
      (cong 𝔹-hom (TwoGroup.comp-hom-unit-left φ))
    𝔹-unit-left {G} {H} φ = funExtSquare _ _ _ _ $ 𝔹G.elimProp (λ _ → 𝔹H.isPropDeloopingSquare) unit-left⋆ where
      module 𝔹G = Delooping ⟨ G ⟩ (str G)
      module 𝔹H = Delooping ⟨ H ⟩ (str H)

      p : (id ⟨ 𝔹-ob G ⟩) ⋆ (𝔹-hom φ) ≡ (𝔹-hom idGroupHom) ⋆ (𝔹-hom φ)
      p = 𝔹-id-lax G hGpdCat.∙ₕ refl′ (𝔹-hom φ)

      q : (𝔹-hom idGroupHom ⋆ 𝔹-hom φ) ≡ 𝔹-hom (compGroupHom idGroupHom φ)
      q = 𝔹-trans-lax idGroupHom φ

      unit-left⋆ : 𝔹G.cong⋆ (p ∙ q) ≡ refl′ 𝔹H.⋆
      unit-left⋆ = 𝔹G.cong⋆-∙ p q ∙ sym compPathRefl

    𝔹-unit-right : (φ : GroupHom G H) → Square
      ((refl′ (𝔹-hom φ) hGpdCat.∙ₕ 𝔹-id-lax H) hGpdCat.∙ᵥ 𝔹-trans-lax φ idGroupHom)
      (refl′ (𝔹-hom φ))
      (hGpdCat.comp-hom-unit-right (𝔹-hom φ))
      (cong 𝔹-hom (TwoGroup.comp-hom-unit-right φ))
    𝔹-unit-right {G} {H} φ = funExtSquare _ _ _ _ $ 𝔹G.elimProp (λ _ → 𝔹H.isPropDeloopingSquare) unit-right⋆ where
      module 𝔹G = Delooping ⟨ G ⟩ (str G)
      module 𝔹H = Delooping ⟨ H ⟩ (str H)

      p = refl′ (𝔹-hom φ) hGpdCat.∙ₕ 𝔹-id-lax H
      q = 𝔹-trans-lax φ idGroupHom

      -- Both p and q reduce to refl at the point:
      unit-right⋆ : 𝔹G.cong⋆ (p ∙ q) ≡ refl′ 𝔹H.⋆
      unit-right⋆ = 𝔹G.cong⋆-∙ p q ∙ sym compPathRefl

  TwoDelooping : LaxFunctor (TwoGroup ℓ) (hGpdCat ℓ)
  TwoDelooping .LaxFunctor.F-ob = 𝔹-ob
  TwoDelooping .LaxFunctor.F-hom = 𝔹-hom
  TwoDelooping .LaxFunctor.F-rel = 𝔹-rel
  TwoDelooping .LaxFunctor.F-rel-id = 𝔹-rel-id
  TwoDelooping .LaxFunctor.F-rel-trans = 𝔹-rel-trans
  TwoDelooping .LaxFunctor.F-trans-lax = 𝔹-trans-lax
  TwoDelooping .LaxFunctor.F-trans-lax-natural = 𝔹-trans-lax-natural
  TwoDelooping .LaxFunctor.F-id-lax = 𝔹-id-lax
  TwoDelooping .LaxFunctor.F-assoc = 𝔹-assoc
  TwoDelooping .LaxFunctor.F-unit-left = 𝔹-unit-left
  TwoDelooping .LaxFunctor.F-unit-right = 𝔹-unit-right
