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
open import Cubical.Data.Sigma as Sigma using (_×_ ; ∃!-syntax)
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Limits.BinProduct

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
    (λ _ → fst fst-hom)
    (λ _ _ → refl)
    λ _ → snd fst-hom

  sndMorphism : Morphism self D
  sndMorphism = mkMorphism self D
    snd
    (λ _ → Sum.inr)
    (λ _ → fst snd-hom)
    (λ _ _ → refl)
    λ _ → snd snd-hom

  open Category (Act {ℓ}) using (_⋆_)
  open Morphism
  open Morphismᴰ

  pairingMorphism : ∀ {Z : ActionContainer ℓ} → Morphism Z C → Morphism Z D → Morphism Z self
  pairingMorphism {Z} f g = mkMorphismBundled _ _ pair-shape pair-hom (pair-pos , pair-pos-equivariant) where
    module Z = ActionContainer Z
    module f = Morphism f
    module g = Morphism g

    pair-shape : Z.Shape → C.Shape × D.Shape
    pair-shape = λ s → f.shape-map s , g.shape-map s

    pair-hom : ∀ z → GroupHom (Z.SymmGroup z) (G×H $ pair-shape z)
    pair-hom z = DirProd.pairingHom _ _ (f.symm-hom z) (g.symm-hom z)

    pair-pos : ∀ z → ⟨ P⊎Q (pair-shape z) ⟩ → Z.Pos z
    pair-pos z = Sum.rec (f.pos-map z) (g.pos-map z)

    pair-pos-equivariant : isEquivariantPosMap Z self pair-pos (fst ∘ pair-hom)
    pair-pos-equivariant z k = funExt $ Sum.elim
      (funExt⁻ $ f.is-equivariant-pos-map z k)
      (funExt⁻ $ g.is-equivariant-pos-map z k)


  module UniversalProperty {Z} (f₁ : Morphism Z C) (f₂ : Morphism Z D) where
    private
      module Z = ActionContainer Z
    pairingFst : pairingMorphism f₁ f₂ ⋆ fstMorphism ≡ f₁
    pairingFst = Morphism≡ _ _ refl refl refl

    pairingSnd : pairingMorphism f₁ f₂ ⋆ sndMorphism ≡ f₂
    pairingSnd = Morphism≡ _ _ refl refl refl

    UP : ∃![ f₁×f₂ ∈ Morphism Z self ] (f₁×f₂ ⋆ fstMorphism ≡ f₁) × (f₁×f₂ ⋆ sndMorphism ≡ f₂)
    UP .fst = pairingMorphism f₁ f₂ , pairingFst , pairingSnd
    UP .snd (f , p₁ , p₂) = Sigma.Σ≡Prop
      (λ f → isProp× (isSetMorphism _ _ _ f₁) (isSetMorphism _ _ _ f₂))
      $ sym $ Morphism≡ _ _ shape-map-path pos-map-path symm-map-path where
        shape-map-path : f .shape-map ≡ pairingMorphism f₁ f₂ .shape-map
        shape-map-path i z .fst = p₁ i .shape-map z
        shape-map-path i z .snd = p₂ i .shape-map z

        pos-map-path : PathP (λ i → ∀ z → C.Pos (shape-map (p₁ i) z) ⊎ D.Pos (shape-map (p₂ i) z) → Z.Pos z)
          (f .pos-map) (pairingMorphism f₁ f₂ .pos-map)
        pos-map-path i z (Sum.inl p) = p₁ i .pos-map z p
        pos-map-path i z (Sum.inr q) = p₂ i .pos-map z q

        symm-map-path : PathP (λ i → ∀ z → Z.Symm z → C.Symm (shape-map (p₁ i) z) × D.Symm (shape-map (p₂ i) z))
          (f .symm-map)
          (λ z k → f₁ .symm-map z k , f₂ .symm-map z k)
        symm-map-path i z k .fst = p₁ i .symm-map z k
        symm-map-path i z k .snd = p₂ i .symm-map z k

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

  binProduct : BinProduct (Act {ℓ}) C D
  binProduct = C×D where
    open BinProduct
    C×D : BinProduct _ C D
    C×D .binProdOb = self
    C×D .binProdPr₁ = fstMorphism
    C×D .binProdPr₂ = sndMorphism
    C×D .univProp = UniversalProperty.UP

open DirectProduct using () renaming (self to _⊗_ ; binProduct to binProducts) public
