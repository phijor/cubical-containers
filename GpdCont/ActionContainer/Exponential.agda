{-# OPTIONS --lossy-unification #-}
open import GpdCont.Prelude hiding (_▷_)

module GpdCont.ActionContainer.Exponential (ℓ : Level) where

open import GpdCont.HomotopySet
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Family.Base using (Fam)
open import GpdCont.Group.DirProd
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.TwoCategory using (GroupAction)
open import GpdCont.GroupAction.Sum using (_⊎Action_)
open import GpdCont.GroupAction.Pi using (ΠActionΣ)

open import Cubical.Foundations.Equiv
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)
open import Cubical.Data.Maybe as Maybe
import      Cubical.Data.Sum as Sum

ActCont : TwoCategory (ℓ-suc ℓ) ℓ ℓ
ActCont = Fam (GroupAction ℓ) ℓ

module ActCont = TwoCategory ActCont
module ActCont₀ (F : TwoCategory.ob ActCont) where
  Shape : hSet _
  Shape = F .fst

  Symm : ⟨ Shape ⟩ → Group ℓ
  Symm s = F .snd s .fst

  Pos : ⟨ Shape ⟩ → hSet ℓ
  Pos s = F .snd s .snd .fst

  action : (s : ⟨ Shape ⟩) → Action (Symm s) (Pos s)
  action s = F .snd s .snd .snd

  action≃ : (s : ⟨ Shape ⟩) → (g : ⟨ Symm s ⟩) → ⟨ Pos s ⟩ ≃ ⟨ Pos s ⟩
  action≃ s g = action s .Action.action g

  _▷_ : {s : ⟨ Shape ⟩} → (g : ⟨ Symm s ⟩) → ⟨ Pos s ⟩ → ⟨ Pos s ⟩
  _▷_ {s} g = equivFun (action≃ s g)

  -- _∼_ : ∀ {ℓX} {X : Type ℓX} {ix : Ix} {s : ⟨ Shape ⟩} → (v w : ⟨ Pos ix s ⟩ → X) → Type _
  -- _∼_ {X} {ix} {s} v w = Σ[ g ∈ ⟨ Symm ix s ⟩ ] PathP (λ i → ua (action≃ ix s g) i → X) v w

private
  MaybeSet : (A : hSet ℓ) → hSet ℓ
  MaybeSet (A , is-set-A) .fst = Maybe A
  MaybeSet (A , is-set-A) .snd = isOfHLevelMaybe 0 is-set-A

  isNothing : {A : Type ℓ} → Maybe A → hSet ℓ
  isNothing nothing = UnitSet _
  isNothing (just _) = EmptySet _

_⊗_ : (F G : ActCont.ob) → ActCont.ob
F ⊗ G = F⊗G where
  module F = ActCont₀ F
  module G = ActCont₀ G

  F⊗G : ActCont.ob
  F⊗G .fst = F.Shape ×Set G.Shape
  F⊗G .snd (s , t) .fst = DirProd (F.Symm s) (G.Symm t)
  F⊗G .snd (s , t) .snd .fst = (F.Pos s) ⊎Set (G.Pos t)
  F⊗G .snd (s , t) .snd .snd = (F.action s) ⊎Action (G.action t)

_⇒_ : (F G : ActCont.ob) → ActCont.ob
F ⇒ G = F⇒G where
  module F = ActCont₀ F
  module G = ActCont₀ G

  Shape : hSet ℓ
  Shape = Σ₂[ u ∈ F.Shape →Set G.Shape ] Π₂[ s ∈ ⟨ F.Shape ⟩ ] (G.Pos (u s) →Set MaybeSet (F.Pos s))

  Symm : ⟨ Shape ⟩ → Group ℓ
  Symm (u , f) = ΠGroup {X = ⟨ F.Shape ⟩} λ s → G.Symm (u s)

  Pos : ⟨ Shape ⟩ → hSet ℓ
  Pos (u , f) = Σ₂[ s ∈ F.Shape ] Σ₂[ q ∈ G.Pos (u s) ] isNothing (f s q)

  actionᴰ : (u : ⟨ F.Shape ⟩ → ⟨ G.Shape ⟩) → (f : ∀ s → ⟨ G.Pos (u s) ⟩ → Maybe ⟨ F.Pos s ⟩)
    → ∀ s → Action (G.Symm (u s)) (ΣSet (G.Pos (u s)) (λ q → isNothing (f s q)))
  actionᴰ u f s .Action.action g .fst (q , prf) = (g G.▷ q) , {! !}
  actionᴰ u f s .Action.action g .snd = {! !}
  actionᴰ u f s .Action.pres· = {! !}

  action : ∀ s* → Action (Symm s*) (Pos s*)
  action (u , f) = ΠActionΣ F.Shape
    (λ s → Σ₂[ q ∈ G.Pos (u s) ] isNothing (f s q))
    (λ s → actionᴰ u f s)

  F⇒G : ActCont.ob
  F⇒G .fst = Shape
  F⇒G .snd s* .fst = Symm s*
  F⇒G .snd s* .snd .fst = Pos s*
  F⇒G .snd s* .snd .snd = action s*

eval : {F G : ActCont.ob} → ActCont.hom (F ⊗ (F ⇒ G)) G
eval {F} {G} = def where
  module F = ActCont₀ F
  module G = ActCont₀ G

  eval-shape : ⟨ F.Shape ⟩ × (Σ[ u ∈ (⟨ F.Shape ⟩ → ⟨ G.Shape ⟩) ] (∀ s → ⟨ G.Pos (u s) ⟩ → Maybe ⟨ F.Pos s ⟩)) → ⟨ G.Shape ⟩
  eval-shape (s , (u , f)) = u s

  eval-pos : ∀ s* → ⟨ G.Pos (eval-shape s*) ⟩ → ⟨ F.Pos (s* .fst) ⊎Set ActCont₀.Pos (F ⇒ G) (s* .snd) ⟩
  eval-pos (s , u , f) q = helper (f s q) refl where
    helper : (p : Maybe ⟨ F.Pos s ⟩) → p ≡ f s q → ⟨ F.Pos s ⊎Set ActCont₀.Pos (F ⇒ G) (u , f) ⟩
    helper nothing eq = Sum.inr (s , q , subst (⟨_⟩ ∘ isNothing) eq tt*)
    helper (just p) eq = Sum.inl p

  def : ActCont.hom _ _
  def .fst = eval-shape
  def .snd s* .fst = {! !}
  def .snd s* .snd .fst = eval-pos s*
  def .snd s* .snd .snd = {! !}
