module GpdCont.SymmetricContainer.WildCat where

open import GpdCont.Prelude hiding (id) renaming (_∘_ to _∘fun_)
open import GpdCont.SymmetricContainer.Base
open import GpdCont.SymmetricContainer.Morphism
open import GpdCont.SymmetricContainer.Eval
open import GpdCont.SymmetricContainer.EvalHom
open import GpdCont.WildCat.NatTrans using (WildNatTransPath)
open import GpdCont.WildCat.TypeOfHLevel
open import GpdCont.WildCat.HomotopyCategory using (ho)

open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Instances.Discrete using (DiscreteCategory)
open import Cubical.WildCat.Base using (WildCat ; _[_,_] ; concatMor)
open import Cubical.WildCat.Functor using (WildFunctor ; WildNatTrans ; compWildNatTrans)
import Cubical.Foundations.GroupoidLaws as GL
import Cubical.Foundations.Transport as Transport

open WildCat hiding (_⋆_)

module _ (ℓ : Level) where
  SymmContWildCat : WildCat (ℓ-suc ℓ) ℓ
  SymmContWildCat .ob = SymmetricContainer ℓ
  SymmContWildCat .Hom[_,_] = Morphism
  SymmContWildCat .id = idMorphism _
  SymmContWildCat .WildCat._⋆_ = compMorphism
  SymmContWildCat .⋆IdL = compMorphismIdL
  SymmContWildCat .⋆IdR = compMorphismIdR
  SymmContWildCat .⋆Assoc = compMorphismAssoc

  hoSymmCont : Category _ _
  hoSymmCont = ho SymmContWildCat

  SymmContLocalCat : (C D : SymmetricContainer ℓ) → Category _ _
  SymmContLocalCat C D = DiscreteCategory (Morphism C D , isGroupoidMorphism)

private
  variable
    ℓ : Level

Eval : (G : SymmetricContainer ℓ) → WildFunctor (hGroupoidCat ℓ) (hGroupoidCat ℓ)
Eval G .WildFunctor.F-ob = ⟦ G ⟧
Eval G .WildFunctor.F-hom {x} {y} = ⟦ G ⟧-map x y
Eval G .WildFunctor.F-id {x} = ⟦ G ⟧-map-id x
Eval G .WildFunctor.F-seq {x} {y} {z} = ⟦ G ⟧-map-comp x y z

module EvalFunctor where
  private
    variable
      G H : SymmetricContainer ℓ

  on-hom : (α : Morphism G H) → WildNatTrans _ _ (Eval G) (Eval H)
  on-hom α .WildNatTrans.N-ob = Hom⟦ α ⟧₀
  on-hom α .WildNatTrans.N-hom {x} {y} = Hom⟦ α ⟧₀-natural x y

  on-hom-id-ob : ∀ (X : hGroupoidCat ℓ .ob) → Hom⟦ idMorphism G ⟧₀ X ≡ id (hGroupoidCat ℓ) {x = ⟦ G ⟧ X}
  on-hom-id-ob {G} X = funExt $ Hom⟦_⟧₀-id {G = G} X

  on-hom-id : on-hom (idMorphism G) ≡ hGroupoidEndo ℓ .id {x = Eval G}
  on-hom-id = WildNatTransPath
    on-hom-id-ob
    λ f i → refl

  open Morphism

  module _ {G H K : SymmetricContainer ℓ} (α : Morphism G H) (β : Morphism H K) where
    on-hom-seq-ob : (X : hGroupoidCat ℓ .ob) → Hom⟦ α ⋆⟨ SymmContWildCat ℓ ⟩ β ⟧₀ X ≡ Hom⟦ β ⟧₀ X ∘fun Hom⟦ α ⟧₀ X
    on-hom-seq-ob X = refl

    on-hom-seq : on-hom (α ⋆⟨ SymmContWildCat ℓ ⟩ β) ≡ on-hom α ⋆⟨ hGroupoidEndo ℓ ⟩ on-hom β
    on-hom-seq = WildNatTransPath
      on-hom-seq-ob λ {x} {y} → goal x y
      where module _ (x y : hGroupoidCat ℓ .ob) (f : hGroupoidCat _ [ x , y ]) where
        p : Path _
          (Hom⟦ β ⟧₀ y ∘fun Hom⟦ α ⟧₀ y ∘fun (⟦ G ⟧-map x y f))
          (Hom⟦ α ⋆⟨ SymmContWildCat ℓ ⟩ β ⟧₀ y ∘fun (⟦ G ⟧-map x y f))
        p i = ⟦ G ⟧-map x y f ⋆⟨hGpd[ ⟦ G ⟧ x , ⟦ G ⟧ y , ⟦ K ⟧ y ]⟩ (on-hom-seq-ob y (~ i))

        q : Path _ _ _
        q = Hom⟦ α ⋆Mor β ⟧₀-natural x y f

        r : Path _
          (⟦ K ⟧-map x y f ∘fun Hom⟦ α ⋆⟨ SymmContWildCat ℓ ⟩ β ⟧₀ x)
          (⟦ K ⟧-map x y f ∘fun Hom⟦ β ⟧₀ x ∘fun Hom⟦ α ⟧₀ x)
        r i = (on-hom-seq-ob x i) ⋆⟨hGpd[ ⟦ G ⟧ x , ⟦ K ⟧ x , ⟦ K ⟧ y ]⟩ ⟦ K ⟧-map x y f

        s : Path _ _ _
        s = ⊛-hom _ (on-hom α) (on-hom β) x y f

        _ : s ≡ p ∙∙ q ∙∙ r
        _ = refl

        goal : PathP (λ i → p (~ i) ≡ r i) q s
        goal = doubleCompPath-filler p q r

EvalFunctor : WildFunctor (SymmContWildCat ℓ) (hGroupoidEndo ℓ)
EvalFunctor .WildFunctor.F-ob = Eval
EvalFunctor .WildFunctor.F-hom = EvalFunctor.on-hom
EvalFunctor .WildFunctor.F-id = EvalFunctor.on-hom-id
EvalFunctor .WildFunctor.F-seq = EvalFunctor.on-hom-seq
