module GpdCont.SymmetricContainer.Substitution where

open import GpdCont.Prelude
open import GpdCont.HLevels
open import GpdCont.HomotopySet
open import GpdCont.SymmetricContainer.Parametrized
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.StrictFunctor
open import GpdCont.TwoCategory.Algebra
open import GpdCont.TwoCategory.Initial

open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)


private
  variable
    ℓ : Level
    Ix : Type ℓ

_[_] : (F : ContainerP⁺¹ Ix) → (G : ContainerP Ix) → ContainerP Ix
F [ G ] = F[G] where
  module F = ContainerP F
  module G = ContainerP G

  F[G] : ContainerP _
  F[G] .ContainerP.Shape = Σʰ[ 3 ∣ s ∈ F.Shape ] (⟨ F.Pos free s ⟩ →₃ G.Shape)
  F[G] .ContainerP.Pos ix (s , f) = F.Pos (param ix) s ⊎Set (Σʰ[ 2 ∣ q ∈ F.Pos free s ] G.Pos ix (f q))
{-# INJECTIVE_FOR_INFERENCE _[_] #-}

subst-map : {F₀ F₁ : ContainerP⁺¹ Ix} {G₀ G₁ : ContainerP Ix}
  → (φ : MorphismP F₀ F₁) (γ : MorphismP G₀ G₁) → MorphismP (F₀ [ G₀ ]) (F₁ [ G₁ ])
subst-map {Ix} {F₀} {F₁} {G₀} {G₁} φ γ = def where
  module φ = MorphismP φ
  module γ = MorphismP γ

  shape-map : ⟨ ContainerP.Shape (F₀ [ G₀ ]) ⟩ → ⟨ ContainerP.Shape (F₁ [ G₁ ]) ⟩
  shape-map (s , f) .fst = the (⟨ ContainerP.Shape F₁ ⟩) (φ.shape-map s)
  shape-map (s , f) .snd = φ.pos-map free s ⋆ f ⋆ γ.shape-map

  pos-map : (ix : Ix) (s* : ⟨ ContainerP.Shape (F₀ [ G₀ ]) ⟩)
    → ⟨ ContainerP.Pos (F₁ [ G₁ ]) ix (shape-map s*) ⟩
    → ⟨ ContainerP.Pos (F₀ [ G₀ ]) ix s* ⟩
  pos-map ix (s , f) = Sum.map φ* φ+γ
    where
    φ* : ⟨ ContainerP.Pos F₁ (param ix) (φ.shape-map s) ⟩ → ⟨ ContainerP.Pos F₀ (param ix) s ⟩
    φ* = φ.pos-map (param ix) s

    φ+γ : (Σ[ p₁ ∈ ⟨ ContainerP.Pos F₁ free (φ.shape-map s) ⟩ ] ⟨ ContainerP.Pos G₁ ix (γ.shape-map (f (φ.pos-map free s p₁))) ⟩)
      → Σ[ p₀ ∈ ⟨ ContainerP.Pos F₀ free s ⟩ ] ⟨ ContainerP.Pos G₀ ix (f p₀) ⟩
    φ+γ (p₁ , q₁) .fst = φ.pos-map free s p₁
    φ+γ (p₁ , q₁) .snd = γ.pos-map ix _ q₁

  def : MorphismP _ _
  def .MorphismP.shape-map = shape-map
  def .MorphismP.pos-map = pos-map

subst-map-id : (F : ContainerP⁺¹ Ix) (G : ContainerP Ix)
  → subst-map (idP F) (idP G) ≡ idP (F [ G ])
subst-map-id F G = MorphismP≡ refl (funExt₃ λ ix s → Sum.elim (refl′ ∘ inl) (refl′ ∘ inr))

substr-map : (F : ContainerP⁺¹ Ix) {G₀ G₁ : ContainerP Ix}
  → (γ : MorphismP G₀ G₁) → MorphismP (F [ G₀ ]) (F [ G₁ ])
substr-map F {G₀} {G₁} γ = subst-def where
  module γ = MorphismP γ

  shape-map : ⟨ ContainerP.Shape (F [ G₀ ]) ⟩ → ⟨ ContainerP.Shape (F [ G₁ ]) ⟩
  shape-map = map-snd λ f → f ⋆ γ.shape-map

  subst-def : MorphismP _ _
  subst-def .MorphismP.shape-map = shape-map
  subst-def .MorphismP.pos-map ix (s , f) = Sum.map
    (id ⟨ ContainerP.Pos F (param ix) s ⟩)
    (map-snd (γ.pos-map ix (f _)))

{- Cool fact: F[γ] and idꟳ[γ] are definitionally the same -}
subst-map≡substr-map : (F : ContainerP⁺¹ Ix) {G₀ G₁ : ContainerP Ix} (γ : MorphismP G₀ G₁)
  → subst-map (idP F) γ ≡ substr-map F γ
subst-map≡substr-map F γ = refl

substr-map-id : (F : ContainerP⁺¹ Ix) (G : ContainerP Ix)
  → substr-map F (idP G) ≡ idP (F [ G ])
substr-map-id F G = MorphismP≡ refl (funExt₃ λ ix s → Sum.elim (refl′ ∘ inl) (refl′ ∘ inr))

substr-map-comp : (F : ContainerP⁺¹ Ix) {G₀ G₁ G₂ : ContainerP Ix}
  → (γ₀ : MorphismP G₀ G₁)
  → (γ₁ : MorphismP G₁ G₂)
  → compP (substr-map F γ₀) (substr-map F γ₁) ≡ substr-map F (compP γ₀ γ₁)
substr-map-comp F γ₀ γ₁ = MorphismP≡ refl (funExt₃ λ { ix (s , f) → Sum.elim (λ _ → refl) (λ _ → refl) })

module _ {Ix : Type ℓ} (F : ContainerP⁺¹ Ix) where
  private
    module ContainerPCat = TwoCategory (ContainerPCat Ix)
    Subst₀ : (G : ContainerP Ix) → ContainerP Ix
    Subst₀ = F [_]
    {-# INJECTIVE_FOR_INFERENCE Subst₀ #-}

  {-# TERMINATING #-}
  Subst : StrictFunctor (ContainerPCat Ix) (ContainerPCat Ix)
  Subst .StrictFunctor.F-ob = Subst₀
  Subst .StrictFunctor.F-hom = substr-map F
  Subst .StrictFunctor.F-rel = cong (substr-map F)
  Subst .StrictFunctor.F-rel-id = refl
  Subst .StrictFunctor.F-rel-trans = cong-∙ (substr-map F)
  Subst .StrictFunctor.F-hom-comp = substr-map-comp F
  Subst .StrictFunctor.F-hom-id = sym ∘ substr-map-id F
  Subst .StrictFunctor.F-assoc-filler-left = Subst-assoc-filler-left where
    postulate
      Subst-assoc-filler-left : _
  Subst .StrictFunctor.F-assoc-filler-right = Subst-assoc-filler-right where
    postulate
      Subst-assoc-filler-right : _
  Subst .StrictFunctor.F-assoc = Subst-assoc where
    postulate
      Subst-assoc : _
  Subst .StrictFunctor.F-unit-left-filler φ .fst = refl
  Subst .StrictFunctor.F-unit-left-filler φ .snd = {! !} -- MorphismPSquare refl (funExtSquare λ ix → funExtSquare λ { (s , f) → funExtSquare (Sum.elim (λ _ → reflSquare _) (λ _ → reflSquare _)) })
  Subst .StrictFunctor.F-unit-left φ = reflSquare _
  Subst .StrictFunctor.F-unit-right-filler φ .fst = refl
  Subst .StrictFunctor.F-unit-right-filler φ .snd = {! !} -- MorphismPSquare refl (funExtSquare λ ix → funExtSquare λ { (s , f) → funExtSquare (Sum.elim (λ _ → reflSquare _) (λ _ → reflSquare _)) })
  Subst .StrictFunctor.F-unit-right φ = reflSquare _

  SubstInitial : Type _
  SubstInitial = InitialAlgebra Subst
  {-# INJECTIVE_FOR_INFERENCE SubstInitial #-}

  isInitialSubst : TwoCategory.ob (Algebra Subst) → Type _
  isInitialSubst = isInitial (Algebra Subst)
  {-# INJECTIVE_FOR_INFERENCE isInitialSubst #-}
