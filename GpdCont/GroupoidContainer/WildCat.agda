module GpdCont.GroupoidContainer.WildCat where

open import GpdCont.Prelude hiding (id) renaming (_∘_ to _∘fun_)
open import GpdCont.GroupoidContainer.Base
open import GpdCont.GroupoidContainer.Morphism
open import GpdCont.GroupoidContainer.Eval
open import GpdCont.GroupoidContainer.EvalHom
open import GpdCont.WildCat.NatTrans using (WildNatTransPath)
open import GpdCont.WildCat.TypeOfHLevel

open import Cubical.WildCat.Base using (WildCat ; _[_,_] ; seq')
open import Cubical.WildCat.Functor using (WildFunctor ; WildNatTrans ; compWildNatTrans)
import Cubical.Foundations.GroupoidLaws as GL
import Cubical.Foundations.Transport as Transport

open WildCat

module _ (ℓ : Level) where
  GContCat : WildCat (ℓ-suc ℓ) (ℓ-suc ℓ)
  GContCat .ob = GCont ℓ
  GContCat .Hom[_,_] = GContMorphism
  GContCat .id = GContId _
  GContCat ._⋆_ = compGContMorphism
  GContCat .⋆IdL = compGContMorphismIdL
  GContCat .⋆IdR = compGContMorphismIdR
  GContCat .⋆Assoc = compGContMorphismAssoc

private
  variable
    ℓ : Level

Eval : (G : GCont ℓ) → WildFunctor (hGroupoidCat ℓ) (hGroupoidCat ℓ)
Eval G .WildFunctor.F-ob = ⟦ G ⟧
Eval G .WildFunctor.F-hom {x} {y} = ⟦ G ⟧-map x y
Eval G .WildFunctor.F-id {x} = ⟦ G ⟧-map-id x
Eval G .WildFunctor.F-seq {x} {y} {z} = ⟦ G ⟧-map-comp x y z

module EvalFunctor where
  private
    variable
      G H : GCont ℓ

  on-hom : (α : GContMorphism G H) → WildNatTrans _ _ (Eval G) (Eval H)
  on-hom α .WildNatTrans.N-ob = Hom⟦ α ⟧₀
  on-hom α .WildNatTrans.N-hom {x} {y} = Hom⟦ α ⟧₀-natural x y

  on-hom-id-ob : ∀ (X : hGroupoidCat ℓ .ob) → Hom⟦ GContId G ⟧₀ X ≡ id (hGroupoidCat ℓ) {x = ⟦ G ⟧ X}
  on-hom-id-ob {G} X = funExt $ Hom⟦_⟧₀-id {G = G} X

  on-hom-id : on-hom (GContId G) ≡ hGroupoidEndo ℓ .id {x = Eval G}
  on-hom-id = WildNatTransPath
    on-hom-id-ob
    λ f i → refl

  open GContMorphism

  module _ {G H K : GCont ℓ} (α : GContMorphism G H) (β : GContMorphism H K) where
    on-hom-seq-ob : (X : hGroupoidCat ℓ .ob) → Hom⟦ α ⋆⟨ GContCat ℓ ⟩ β ⟧₀ X ≡ Hom⟦ β ⟧₀ X ∘fun Hom⟦ α ⟧₀ X
    on-hom-seq-ob X = refl

    on-hom-seq : on-hom (α ⋆⟨ GContCat ℓ ⟩ β) ≡ on-hom α ⋆⟨ hGroupoidEndo ℓ ⟩ on-hom β
    on-hom-seq = WildNatTransPath
      on-hom-seq-ob λ {x} {y} → goal x y
      where module _ (x y : hGroupoidCat ℓ .ob) (f : hGroupoidCat _ [ x , y ]) where
        p : Path _
          (Hom⟦ β ⟧₀ y ∘fun Hom⟦ α ⟧₀ y ∘fun (⟦ G ⟧-map x y f))
          (Hom⟦ α ⋆⟨ GContCat ℓ ⟩ β ⟧₀ y ∘fun (⟦ G ⟧-map x y f))
        p i = ⟦ G ⟧-map x y f ⋆⟨hGpd[ ⟦ G ⟧ x , ⟦ G ⟧ y , ⟦ K ⟧ y ]⟩ (on-hom-seq-ob y (~ i))

        q : Path _ _ _
        q = Hom⟦ compGContMorphism α β ⟧₀-natural x y f

        r : Path _
          (⟦ K ⟧-map x y f ∘fun Hom⟦ α ⋆⟨ GContCat ℓ ⟩ β ⟧₀ x)
          (⟦ K ⟧-map x y f ∘fun Hom⟦ β ⟧₀ x ∘fun Hom⟦ α ⟧₀ x)
        r i = (on-hom-seq-ob x i) ⋆⟨hGpd[ ⟦ G ⟧ x , ⟦ K ⟧ x , ⟦ K ⟧ y ]⟩ ⟦ K ⟧-map x y f

        s : Path _ _ _
        s = ⊛-hom _ (on-hom α) (on-hom β) x y f

        _ : s ≡ p ∙∙ q ∙∙ r
        _ = refl

        goal : PathP (λ i → p (~ i) ≡ r i) q s
        goal = doubleCompPath-filler p q r

EvalFunctor : WildFunctor (GContCat ℓ) (hGroupoidEndo ℓ)
EvalFunctor .WildFunctor.F-ob = Eval
EvalFunctor .WildFunctor.F-hom = EvalFunctor.on-hom
EvalFunctor .WildFunctor.F-id = EvalFunctor.on-hom-id
EvalFunctor .WildFunctor.F-seq = EvalFunctor.on-hom-seq
