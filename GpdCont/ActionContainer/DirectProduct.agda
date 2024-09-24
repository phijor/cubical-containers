module GpdCont.ActionContainer.DirectProduct where

open import GpdCont.Prelude hiding (_⋆_)
open import GpdCont.Univalence
open import GpdCont.ActionContainer.Abstract
open import GpdCont.ActionContainer.Morphism
open import GpdCont.ActionContainer.Transformation
open import GpdCont.ActionContainer.Category using (Act)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Sum
open import GpdCont.HomotopySet using (ΠSet ; _×Set_ ; _⊎Set_)
open import GpdCont.Group.DirProd using (DirProd ; module DirProd)
open import GpdCont.Equiv using (equivΠCodComp)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma as Sigma using (_×_)
open import Cubical.Data.Sum as Sum using ()
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Categories.Category.Base using (Category)

private
  variable
    ℓ : Level

module DirectProduct (C D : ActionContainer ℓ) where
  private
    module C = ActionContainer C
    module D = ActionContainer D

    S×T : hSet _
    S×T = C.ShapeSet ×Set D.ShapeSet

    P⊎Q : ⟨ S×T ⟩ → hSet _
    P⊎Q (s , t) = C.PosSet s ⊎Set D.PosSet t

    G×H : ⟨ S×T ⟩ → Group _
    G×H (s , t) = DirProd (C.SymmGroup s) (D.SymmGroup t)

    module G×H {s,t : ⟨ S×T ⟩} = DirProd (C.SymmGroup (s,t .fst)) (D.SymmGroup (s,t .snd))

    σ⊎τ : (x : ⟨ S×T ⟩) → Action (G×H x) (P⊎Q x)
    σ⊎τ (s , t) = C.symmAction s ⊎Action D.symmAction t

  self : ActionContainer ℓ
  self = mkActionContainer S×T P⊎Q G×H σ⊎τ

  private
    fst-hom : ∀ {x} → GroupHom (G×H x) (C.SymmGroup (fst x))
    fst-hom = G×H.fstHom

    snd-hom : ∀ {x} → GroupHom (G×H x) (D.SymmGroup (snd x))
    snd-hom = G×H.sndHom

  fstMorphism : Morphism self C
  fstMorphism = mkMorphism self C
    fst
    (λ _ → Sum.inl)
    (fst fst-hom)
    (λ _ _ → refl)
    λ _ → snd fst-hom

  sndMorphism : Morphism self D
  sndMorphism = mkMorphism self D
    snd
    (λ _ → Sum.inr)
    (fst snd-hom)
    (λ _ _ → refl)
    λ _ → snd snd-hom

  open Category (Act {ℓ}) using (_⋆_)
  open Morphism
  open Morphismᴰ

  pairingMorphism : ∀ {Z : ActionContainer ℓ} → Morphism Z C → Morphism Z D → Morphism Z self
  pairingMorphism f g .shape-map = λ s → f .Morphism.shape-map s , g .Morphism.shape-map s
  pairingMorphism f g .mor-str .pos-map s = Sum.rec (f .pos-map s) (g .pos-map s)
  pairingMorphism f g .mor-str .symm-map = {! !}
  pairingMorphism f g .mor-str .is-group-hom-symm-map = {! !}
  pairingMorphism f g .mor-str .is-equivariant-pos-map = {! !}

  UP₁ : ∀ {Z : ActionContainer ℓ} (f : Morphism Z C) (g : Morphism Z D) → TransformationP (pairingMorphism f g ⋆ fstMorphism) f × TransformationP (pairingMorphism f g ⋆ sndMorphism) g
  UP₁ f g .fst = mkTransformationP refl {conjugator₀ = λ _ → C.symm-id} refl {! !} λ s → ua→ {! !}
  UP₁ f g .snd = mkTransformationP refl {conjugator₀ = λ _ → D.symm-id} refl {! !} λ s → ua→ {! !}

  UP₂ : {! !}
  UP₂ = {! !}

  -- prodMorphism : ∀ {Z : ActionContainer ℓ} → Morphism Z self → Morphism Z C × Morphism Z D
  -- prodMorphism f×g .fst = f×g ⋆ fstMorphism
  -- prodMorphism f×g .snd = f×g ⋆ sndMorphism

  -- fstTransformation : (π₁ : Morphism self C) → TransformationP π₁ fstMorphism
  -- fstTransformation π₁ .TransformationP.shape-path = funExt {! !}
  -- fstTransformation π₁ .TransformationP.conjugator₀ = {! !}
  -- fstTransformation π₁ .TransformationP.conjugator₁ = {! !}
  -- fstTransformation π₁ .TransformationP.conjugator-path = {! !}
  -- fstTransformation π₁ .TransformationP.is-conjugate = {! !}
  -- fstTransformation π₁ .TransformationP.is-pos-equiv = {! !}

open DirectProduct using () renaming (self to _⊗_) public
