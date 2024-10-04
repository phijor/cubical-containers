module GpdCont.ActionContainer.Constant where

open import GpdCont.Prelude
open import GpdCont.HomotopySet
open import GpdCont.Group.DirProd using (module DirProd) renaming (DirProd to _×Group_)

open import GpdCont.GroupAction.Base using (Action)
open import GpdCont.GroupAction.Trivial using (trivialAction)
open import GpdCont.GroupAction.Pi using (ΠActionΣ)
open import GpdCont.ActionContainer.Abstract
open import GpdCont.ActionContainer.Morphism
open import GpdCont.ActionContainer.Category
open import GpdCont.ActionContainer.DirectProduct using (_⊗_ ; binProducts)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (flip)
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv using (funExt₂)
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Empty using (⊥*)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (GroupIso→GroupHom ; invGroupIso ; makeIsGroupHom) renaming (compGroupHom to _⋆Group_)
open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup ; lUnitGroupIso^)
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)

open import Cubical.Categories.Exponentials
open import Cubical.Categories.Presheaf.Representable using (UniversalElement)



private
  variable
    ℓ : Level

  projΠGroupHom : ∀ {ℓK} {K : Type ℓK} (G : K → Group ℓ) → ∀ k → GroupHom (ΠGroup G) (G k)
  projΠGroupHom G k .fst = _$ k
  projΠGroupHom G k .snd .IsGroupHom.pres· _ _ = refl
  projΠGroupHom G k .snd .IsGroupHom.pres1 = refl
  projΠGroupHom G k .snd .IsGroupHom.presinv _ = refl

  lUnitHom : (G : Group ℓ) → GroupHom (UnitGroup {ℓ} ×Group G) G
  lUnitHom G = GroupIso→GroupHom lUnitGroupIso^

  lUnitInv : (G : Group ℓ) → GroupHom G (UnitGroup {ℓ} ×Group G)
  lUnitInv G = GroupIso→GroupHom $ invGroupIso lUnitGroupIso^

  pointwise : ∀ {ℓK} (K : Type ℓK) (H : Group ℓ) → Group (ℓ-max ℓK ℓ)
  pointwise K H = ind where
    module H = GroupStr (str H)

    ind : Group _
    ind .fst = K → ⟨ H ⟩
    ind .snd .GroupStr.1g = const H.1g
    ind .snd .GroupStr._·_ = λ f g k → f k H.· g k
    ind .snd .GroupStr.inv = λ f k → H.inv (f k)
    ind .snd .GroupStr.isGroup = makeIsGroup {! !} {! !} {! !} {! !} {! !} {! !}


konst : (S : hSet ℓ) → ActionContainer ℓ
konst {ℓ} S = mkActionContainer S 𝟘 𝟙 triv where
  𝟘 : ⟨ S ⟩ → hSet ℓ
  𝟘 _ = EmptySet ℓ

  𝟙 : ⟨ S ⟩ → Group ℓ
  𝟙 _ = UnitGroup

  triv : ∀ s → Action (𝟙 s) (𝟘 s)
  triv s = trivialAction (𝟙 s) (𝟘 s)

[konst_,_] : (K : hSet ℓ) → (C : ActionContainer ℓ) → ActionContainer ℓ
[konst K , C ] using (S , P , G , σ) ← unbundleContainer C
  = mkActionContainer S* P* G* σ* where

  S* : hSet _
  S* = K →Set S

  P* : ⟨ S* ⟩ → hSet _
  P* f = ΣSet K (P ∘ f)

  G* : ⟨ S* ⟩ → Group _
  G* f = ΠGroup (G ∘ f)

  σ* : ∀ f → Action (G* f) (P* f)
  σ* f = ΠActionΣ K (P ∘ f) (σ ∘ f)

eval : {K : hSet ℓ} {C : ActionContainer ℓ}
  → Morphism (konst K ⊗ [konst K , C ]) C
eval {K} {C} using (S , P , G , σ) ← unbundleContainer C =
  mkMorphismBundled _ _ eval-shape eval-hom (eval-pos , eval-pos-is-eqva) where
  module C = ActionContainer C
  Thunk = ⟨ K ⟩ × (⟨ K ⟩ → ⟨ S ⟩)

  eval-shape : Thunk → ⟨ S ⟩
  eval-shape (k , f) = f k

  eval-hom : ∀ ((k , f) : Thunk) → GroupHom (UnitGroup ×Group ΠGroup (G ∘ f)) (G (f k))
  eval-hom (k , f) = lUnitHom (ΠGroup (G ∘ f)) ⋆Group (projΠGroupHom (G ∘ f) k)

  eval-pos : ((k , f) : Thunk) → C.Pos (f k) → ⊥* ⊎ (Σ[ k ∈ ⟨ K ⟩ ] ⟨ P (f k) ⟩)
  eval-pos (k , f) p = Sum.inr (k , p)

  eval-pos-is-eqva : isEquivariantPosMap (konst K ⊗ [konst K , C ]) C eval-pos (fst ∘ eval-hom)
  eval-pos-is-eqva (f , k) g* = refl

module _ (K : hSet ℓ) (C Z : ActionContainer ℓ) where
  private
    module C = ActionContainer C
    module Z = ActionContainer Z

    open Morphism
    open Morphismᴰ

    ⊥-⊎-Pos-Iso : ∀ z → Iso (⊥* {ℓ = ℓ} ⊎ Z.Pos z) (Z.Pos z)
    ⊥-⊎-Pos-Iso z = Sum.⊎-IdL-⊥*-Iso

  konst-uncurry : Morphism Z [konst K , C ] → Morphism (konst K ⊗ Z) C
  konst-uncurry f = go where
    module f = Morphism f

    uncurry-shape : ⟨ K ⟩ × Z.Shape → C.Shape
    uncurry-shape = uncurry $ flip f.shape-map

    uncurry-hom' : ∀ ((k , z) : ⟨ K ⟩ × Z.Shape) → GroupHom (Z.SymmGroup z) (C.SymmGroup (f.shape-map z k))
    uncurry-hom' (k , z) = f.symm-hom z ⋆Group projΠGroupHom (C.SymmGroup ∘ f.shape-map z) k

    uncurry-hom : ∀ ((k , z) : ⟨ K ⟩ × Z.Shape) → GroupHom (UnitGroup ×Group (Z.SymmGroup z)) (C.SymmGroup (f.shape-map z k))
    uncurry-hom (k , z) = lUnitHom _ ⋆Group uncurry-hom' (k , z)

    uncurry-pos : ∀ ((k , z) : ⟨ K ⟩ × Z.Shape) → C.Pos (f.shape-map z k) → ⊥* ⊎ Z.Pos z
    uncurry-pos (k , z) p = ⊥-⊎-Pos-Iso z .Iso.inv (f.pos-map z (k , p))

    uncurry-pos-is-equivariant : isEquivariantPosMap (konst K ⊗ Z) C uncurry-pos (fst ∘ uncurry-hom)
    uncurry-pos-is-equivariant (k , z) (_ , g) = funExt λ p → cong (⊥-⊎-Pos-Iso z .Iso.inv) $ funExt⁻ (f.is-equivariant-pos-map z g) (k , p)

    go : Morphism (konst K ⊗ Z) C
    go = mkMorphismBundled (konst K ⊗ Z) C
      uncurry-shape
      uncurry-hom
      (uncurry-pos , uncurry-pos-is-equivariant)

  konst-curry : Morphism (konst K ⊗ Z) C → Morphism Z [konst K , C ]
  konst-curry f = mkMorphismBundled Z [konst K , C ] curry-shape curry-hom (curry-pos , curry-pos-is-equivariant) where
    module f = Morphism f

    curry-shape : Z.Shape → ⟨ K ⟩ → C.Shape
    curry-shape = flip $ curry f.shape-map

    module Gᶻ {z} = GroupStr (str (Z.SymmGroup z))
    module Gᶜ {c} = GroupStr (str (C.SymmGroup c))

    curry-hom : ∀ z → GroupHom (Z.SymmGroup z) (ΠGroup (C.SymmGroup ∘ curry-shape z))
    curry-hom z .fst gᶻ k = f.symm-map (k , z) (tt* , gᶻ)
    curry-hom z .snd = makeIsGroupHom λ gᶻ hᶻ → funExt λ k →
      let φ = f.symm-map (k , z) in
      φ (tt* , gᶻ Gᶻ.· hᶻ) ≡⟨ f.is-group-hom-symm-map (k , z) .IsGroupHom.pres· (tt* , gᶻ) (tt* , hᶻ) ⟩
      (φ (tt* , gᶻ)) Gᶜ.· (φ (tt* , hᶻ)) ∎

    curry-pos : ∀ z → Σ[ k ∈ ⟨ K ⟩ ] C.Pos (f.shape-map (k , z)) → Z.Pos z
    curry-pos z (k , p) = del-⊥ (f.pos-map (k , z) p) where
      del-⊥ : ⊥* ⊎ Z.Pos z → Z.Pos z
      del-⊥ = Sum.⊎-IdL-⊥*-Iso .Iso.fun

    curry-pos-is-equivariant : isEquivariantPosMap Z [konst K , C ] curry-pos (fst ∘ curry-hom)
    curry-pos-is-equivariant z gᶻ = funExt λ where
      (k , c-pos) →
        equivFun (Z.action gᶻ) (curry-pos z (k , c-pos)) ≡[ i ]⟨ {! !} ⟩
        curry-pos z (k , equivFun (C.action (f.symm-map (k , z) (tt* , gᶻ))) c-pos) ∎

  konst-curry-Iso : Iso (Morphism Z [konst K , C ]) (Morphism (konst K ⊗ Z) C)
  konst-curry-Iso .Iso.fun = konst-uncurry
  konst-curry-Iso .Iso.inv = konst-curry
  konst-curry-Iso .Iso.rightInv f× = Morphism≡ _ _ refl (funExt₂ pos-path) refl where
    pos-path : ∀ ((k , z) : ⟨ K ⟩ × ⟨ Z.ShapeSet ⟩) (c-pos : C.Pos (shape-map f× (k , z))) → Sum.inr (pos-map (konst-curry f×) z (k , c-pos)) ≡ pos-map f× (k , z) c-pos
    pos-path (k , z) c-pos = Sum.⊎-IdL-⊥*-Iso .Iso.leftInv (pos-map (mor-str f×) (k , z) c-pos)
  konst-curry-Iso .Iso.leftInv f→ = Morphism≡ _ _ refl refl refl

konst-exponential : (K : hSet ℓ) (C : ActionContainer ℓ) → Exponential (Act {ℓ}) (konst K) C (binProducts $ konst K)
konst-exponential K C = K⇒C where
  uncurry' : ∀ Z → Morphism Z [konst K , C ] → Morphism (konst K ⊗ Z) C
  uncurry' Z f .Morphism.shape-map = λ z → Morphism.shape-map f (z .snd) (z .fst)
  uncurry' Z f .Morphism.mor-str .Morphismᴰ.pos-map = λ s z → Sum.inr ((Morphism.pos-map f) (snd s) (fst s , z))
  uncurry' Z f .Morphism.mor-str .Morphismᴰ.symm-map = λ s z → Morphism.symm-map f (snd s) (snd z) (fst s)
  uncurry' Z f .Morphism.mor-str .Morphismᴰ.is-group-hom-symm-map = _
  uncurry' Z f .Morphism.mor-str .Morphismᴰ.is-equivariant-pos-map = _

  konst-universal : ∀ (Z : ActionContainer _) → isEquiv (konst-uncurry K C Z)
  konst-universal Z = isoToIsEquiv (konst-curry-Iso K C Z)

  opaque
    p : ∀ Z → konst-uncurry K C Z ≡ uncurry' Z
    p Z = funExt λ f → Morphism≡ _ _ refl refl refl

  universal : ∀ (Z : ActionContainer _) → isEquiv (uncurry' Z)
  universal Z = subst isEquiv (p Z) (konst-universal Z)

  K⇒C : Exponential Act (konst K) C (binProducts $ konst K)
  K⇒C .UniversalElement.vertex = [konst K , C ]
  K⇒C .UniversalElement.element = eval {K = K} {C = C}
  K⇒C .UniversalElement.universal = universal
