open import GpdCont.Prelude hiding (_▷_)

module GpdCont.ActionContainer.Parametrized (ℓ : Level) where

open import GpdCont.HomotopySet
open import GpdCont.Univalence
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Displayed.Base using (module TotalTwoCategory)
open import GpdCont.TwoCategory.Family.Base using (Fam)
open import GpdCont.TwoCategory.Product using (Δ)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Orbit using (OrbitSet)
open import GpdCont.GroupAction.Equivariant using (isEquivariantMap[_][_,_])
open import GpdCont.GroupAction.TwoCategory using (GroupAction)
open import GpdCont.Group.Pi using (mapΠGroup)

open import Cubical.Foundations.Equiv
import      Cubical.Data.Equality as Eq
open import Cubical.Data.Maybe
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms

private
  variable
    ℓIx : Level
    Ix : Type ℓIx

module _ {ℓIx} (Ix : Type ℓIx) where
  ActCont : TwoCategory (ℓ-max (ℓ-suc ℓ) ℓIx) (ℓ-max ℓ ℓIx) (ℓ-max ℓ ℓIx)
  ActCont = Fam (Δ Ix (GroupAction ℓ)) ℓ

  module ActCont = TwoCategory ActCont

module ActCont₀ {ℓIx} {Ix : Type ℓIx} (F : ActCont.ob Ix) where
  Shape : hSet _
  Shape = F .fst

  Symm : Ix → ⟨ Shape ⟩ → Group ℓ
  Symm ix s = F .snd s ix .fst

  Pos : Ix → ⟨ Shape ⟩ → hSet ℓ
  Pos ix s = F .snd s ix .snd .fst

  action : (ix : Ix) → (s : ⟨ Shape ⟩) → Action (Symm ix s) (Pos ix s)
  action ix s = F .snd s ix .snd .snd

  action≃ : (ix : Ix) → (s : ⟨ Shape ⟩) → (g : ⟨ Symm ix s ⟩) → ⟨ Pos ix s ⟩ ≃ ⟨ Pos ix s ⟩
  action≃ ix s g = action ix s .Action.action g

  module _ {ix : Ix} {s : ⟨ Shape ⟩} where
    private
      module Symm = GroupStr (str (Symm ix s))
    open Symm using (_·_ ; inv) public

    _▷_ : (g : ⟨ Symm ix s ⟩) → ⟨ Pos ix s ⟩ → ⟨ Pos ix s ⟩
    _▷_ g = equivFun (action≃ ix s g)

    ·-▷-assoc : (g h : ⟨ Symm ix s ⟩) (p : ⟨ Pos ix s ⟩) → (g · h) ▷ p ≡ h ▷ (g ▷ p)
    ·-▷-assoc g h p = ActionProperties.action-comp (action ix s) g h ≡$ p

    _∼_ : ∀ {ℓX} {X : Type ℓX} → (v w : ⟨ Pos ix s ⟩ → X) → Type _
    _∼_ {X} v w = Σ[ g ∈ ⟨ Symm ix s ⟩ ] PathP (λ i → ua (action≃ ix s g) i → X) v w

module _ {ℓIx} (Ix : Type ℓIx) where
  _+1 : Type ℓIx
  _+1 = Maybe Ix

  ActCont[_+1] : Type _
  ActCont[_+1] = ActCont.ob (_+1)

pattern free = nothing
pattern param ix = just ix

module ActCont₁ {ℓIx} {Ix : Type ℓIx} {F G : ActCont.ob Ix} (f : ActCont.hom Ix F G) where
  private
    module F = ActCont₀ F
    module G = ActCont₀ G

  shape-map : ⟨ F.Shape ⟩ → ⟨ G.Shape ⟩
  shape-map = f .fst

  symm-map : ∀ ix s → GroupHom (F.Symm ix s) (G.Symm ix (shape-map s))
  symm-map ix s = f .snd s ix .fst

  pos-map : ∀ ix s → ⟨ G.Pos ix (shape-map s) ⟩ → ⟨ F.Pos ix s ⟩
  pos-map ix s = f .snd s ix .snd .fst

  is-hom : ∀ ix s → isEquivariantMap[ symm-map ix s , pos-map ix s ][ F.action ix s , G.action ix (shape-map s) ]
  is-hom ix s = f .snd s ix .snd .snd

module ActCont+1₀ {ℓIx} {Ix : Type ℓIx} (F : ActCont[ Ix +1]) where
  open ActCont₀ F public

  Free : ⟨ Shape ⟩ → hSet _
  Free = Pos free

  Param : Ix → ⟨ Shape ⟩ → hSet _
  Param = Pos ∘ param

  Free/ : ⟨ Shape ⟩ → hSet _
  Free/ = OrbitSet ∘ action free
