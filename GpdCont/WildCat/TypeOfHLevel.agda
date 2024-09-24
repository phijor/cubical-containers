module GpdCont.WildCat.TypeOfHLevel where

open import GpdCont.Prelude renaming (id to idfun)
open import GpdCont.WildCat.Subtype
open import GpdCont.WildCat.NatTrans
open import GpdCont.WildCat.FunctorCategory public

open import Cubical.Foundations.Function using (flip) renaming (_∘_ to _∘fun_)
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.Base using (WildCat ; _[_,_] ; concatMor)
open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Instances.Types using (TypeCat)
import Cubical.Foundations.GroupoidLaws as GL

module _ (ℓ : Level) where
  open WildCat hiding (_⋆_)

  TypeOfHLevelCat : (n : HLevel) → WildCat (ℓ-suc ℓ) ℓ
  TypeOfHLevelCat n = SubtypeCat (TypeCat ℓ) (isOfHLevel n)

  hGroupoidCat : WildCat (ℓ-suc ℓ) ℓ
  hGroupoidCat = TypeOfHLevelCat 3

  private
    𝕋 = TypeCat ℓ
    module 𝕋 = WildCat 𝕋
    𝔾 = hGroupoidCat
    module 𝔾 = WildCat 𝔾

    Nat : (F G : WildFunctor hGroupoidCat hGroupoidCat) → Type _
    Nat F G = WildNatTrans _ _ F G

    idNat : (F : WildFunctor hGroupoidCat hGroupoidCat) → Nat F F
    idNat F .WildNatTrans.N-ob x = idfun (F .WildFunctor.F-ob x .fst)
    idNat F .WildNatTrans.N-hom f = refl

  module composite {F G H : WildFunctor hGroupoidCat hGroupoidCat} (α : Nat F G) (β : Nat G H) where
    module G = WildFunctor G
    module F = WildFunctor F
    module H = WildFunctor H
    module α = WildNatTrans α
    module β = WildNatTrans β

    composite-ob : (x : hGroupoidCat .ob) → hGroupoidCat [ F.F-ob x , H.F-ob x ]
    composite-ob x = (β.N-ob x) ∘fun (α.N-ob x)

    composite-hom : ∀ (x y : hGroupoidCat .ob) (f : hGroupoidCat [ x , y ])
      → (composite-ob y) ∘fun (F.F-hom f) ≡ H.F-hom f ∘fun (composite-ob x)
    composite-hom x y f = congS ((β.N-ob y) ∘fun_) (α.N-hom f) ∙ congS (_∘fun α.N-ob x) (β.N-hom f)

    composite : Nat F H
    composite .WildNatTrans.N-ob = composite-ob
    composite .WildNatTrans.N-hom {x} {y} = composite-hom x y

  open composite using () renaming (composite to _⊛_ ; composite-hom to ⊛-hom) public

  idNatTransₗ : ∀ {F G : WildFunctor hGroupoidCat hGroupoidCat} (α : Nat F G) → (idNat F) ⊛ α ≡ α
  idNatTransₗ {F} {G} α = WildNatTransPath
    (λ x → refl)
    (λ {x} {y} f → sym (GL.lUnit $ α .WildNatTrans.N-hom f))

  idNatTransᵣ : ∀ {F G : WildFunctor hGroupoidCat hGroupoidCat} (α : Nat F G) → α ⊛ (idNat G) ≡ α
  idNatTransᵣ {F} {G} α = WildNatTransPath
    (λ x → refl)
    (λ {x} {y} f → sym (GL.rUnit $ α .WildNatTrans.N-hom f))

  assocNatTrans : ∀ {F G H K : WildFunctor hGroupoidCat hGroupoidCat} (α : Nat F G) (β : Nat G H) (γ : Nat H K) →
    (α ⊛ β) ⊛ γ
      ≡
    α ⊛ (β ⊛ γ)
  assocNatTrans {F} {G} {H} {K} α β γ = WildNatTransPath (λ x → refl) assoc where
    module F = WildFunctor F
    module G = WildFunctor G
    module H = WildFunctor H
    module K = WildFunctor K

    open WildNatTrans

    assoc : ∀ {x y} f → composite.composite-hom (α ⊛ β) γ x y f ≡ composite.composite-hom α (β ⊛ γ) x y f
    assoc {x} {y} f =
      congS ((γ .N-ob y) ∘fun_) ((α ⊛ β) .N-hom f) ∙ congS (_∘fun (α ⊛ β) .N-ob x) (γ .N-hom f)
        ≡⟨ cong (_∙ cong (_∘fun (α ⊛ β) .N-ob x) (γ .N-hom f)) (GL.cong-∙ (γ .N-ob y ∘fun_) _ _) ⟩
      (_ ∙ _) ∙ cong (_∘fun (α ⊛ β) .N-ob x) (γ .N-hom f)
        ≡⟨ sym (GL.assoc _ _ _) ⟩
      congS (((β ⊛ γ) .N-ob y) ∘fun_) (α .N-hom f) ∙ _
        ≡⟨ cong (cong (((β ⊛ γ) .N-ob y) ∘fun_) (α .N-hom f) ∙_) (sym (GL.cong-∙ (_∘fun α .N-ob x) (congS ((γ .N-ob _) ∘fun_) (β .N-hom f)) (congS (_∘fun β .N-ob _) (γ .N-hom f))) )⟩
      congS (((β ⊛ γ) .N-ob y) ∘fun_) (α .N-hom f)
        ∙ congS (_∘fun α .N-ob x) (
          congS ((γ .N-ob _) ∘fun_) (β .N-hom f)
          ∙ congS (_∘fun β .N-ob _) (γ .N-hom f)
        )
        ∎

  hGroupoidEndo : WildCat (ℓ-suc ℓ) (ℓ-suc ℓ)
  hGroupoidEndo .ob = WildFunctor hGroupoidCat hGroupoidCat
  hGroupoidEndo .Hom[_,_] = WildNatTrans hGroupoidCat hGroupoidCat
  hGroupoidEndo .id = idNat _
  hGroupoidEndo .WildCat._⋆_ = _⊛_
  hGroupoidEndo .⋆IdL = idNatTransₗ
  hGroupoidEndo .⋆IdR = idNatTransᵣ
  hGroupoidEndo .⋆Assoc = assocNatTrans

open WildCat hiding (_⋆_)
hseq' : ∀ {ℓ} (x y z : hGroupoidCat ℓ .ob) (f : hGroupoidCat ℓ [ x , y ]) (g : hGroupoidCat ℓ [ y , z ]) → hGroupoidCat ℓ [ x , z ]
hseq' x y z = concatMor (hGroupoidCat _) {x = x} {y = y} {z = z}
syntax hseq' x y z f g = f ⋆⟨hGpd[ x , y , z ]⟩ g
