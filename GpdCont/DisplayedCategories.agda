module GpdCont.DisplayedCategories where

open import GpdCont.Prelude
open import GpdCont.Univalence
import GpdCont.HomotopySet as HSet

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism as Iso using ()
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using ()

open import Cubical.Categories.Category.Base using (Category ; _[_,_] ; seq')
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Equivalence.Base using (_≃ᶜ_)
open import Cubical.Categories.Equivalence.AdjointEquivalence using (AdjointEquivalence)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Limits.BinProduct as BP using (BinProducts)
open import Cubical.Categories.Limits.BinProduct.More as BP
open import Cubical.Categories.NaturalTransformation as NT using (NatIso)
open import Cubical.Categories.Constructions.TotalCategory.Base using (∫C)
open import Cubical.Categories.Displayed.Base as Disp using (Categoryᴰ)
open import Cubical.Categories.Displayed.Constructions.TotalCategory using (∫Cᴰ)
open import Cubical.Categories.Displayed.Limits.BinProduct as BPᴰ using ()
open import Cubical.Categories.Exponentials as Exp

module _ {ℓo ℓh ℓo′ ℓh′} (C : Category ℓo ℓh) (D : Category ℓo′ ℓh′) where
  private
    module D = Category D

  constᴰ : Categoryᴰ C ℓo′ ℓh′
  constᴰ .Categoryᴰ.ob[_] = const D.ob
  constᴰ .Categoryᴰ.Hom[_][_,_] = const D.Hom[_,_]
  constᴰ .Categoryᴰ.idᴰ = D.id
  constᴰ .Categoryᴰ._⋆ᴰ_ = D._⋆_
  constᴰ .Categoryᴰ.⋆IdLᴰ = D.⋆IdL
  constᴰ .Categoryᴰ.⋆IdRᴰ = D.⋆IdR
  constᴰ .Categoryᴰ.⋆Assocᴰ = D.⋆Assoc
  constᴰ .Categoryᴰ.isSetHomᴰ = D.isSetHom

module _ (ℓ : Level) {ℓo ℓh} (C : Category ℓo ℓh) where
  private
    module C = Category C

  open Categoryᴰ
  
  Famᴰ : Categoryᴰ (SET ℓ) (ℓ-max ℓo ℓ) (ℓ-max ℓh ℓ)
  Famᴰ .ob[_] X = ⟨ X ⟩ → C.ob
  Famᴰ .Hom[_][_,_] {x = J} {y = K} f Xⱼ Yₖ = ∀ (j : ⟨ J ⟩) → C.Hom[ (Xⱼ j) , Yₖ (f j) ]
  Famᴰ .idᴰ j = C.id
  Famᴰ ._⋆ᴰ_ {f} φ ψ = λ j → φ j C.⋆ ψ (f j)
  Famᴰ .⋆IdLᴰ φ = funExt λ j → C.⋆IdL (φ j)
  Famᴰ .⋆IdRᴰ φ = funExt λ j → C.⋆IdR (φ j)
  Famᴰ .⋆Assocᴰ φ ψ υ = funExt λ j → C.⋆Assoc (φ j) (ψ _) (υ _)
  Famᴰ .isSetHomᴰ = isSetΠ λ j → C.isSetHom

  Fam = ∫C Famᴰ
  {-# INJECTIVE_FOR_INFERENCE Fam #-}
  {-# INJECTIVE_FOR_INFERENCE Famᴰ #-}

  Fam≡ : ∀ {x@(J , X) y@(K , Y) : Category.ob Fam} → (p : J ≡ K) → (q : PathP (λ i → ⟨ p i ⟩ → C.ob) X Y) → x ≡ y
  Fam≡ p q i .fst = p i
  Fam≡ p q i .snd = q i

  FamHom≡ : ∀ {X Y} {f×φ@(f , φ) g×ψ@(g , ψ) : Fam [ X , Y ]}
    → (p : f ≡ g)
    → (∀ j → PathP (λ i → C [ X .snd j , Y .snd (p i j) ]) (φ j) (ψ j))
    → f×φ ≡ g×ψ
  FamHom≡ p q i = p i , λ { j → q j i }

  -- foo : ∀ {I J} {X Y} → Fam [ (I , X) , (J , Y) ] ≡ ((i : ⟨ I ⟩) → Σ[ j ∈ ⟨ J ⟩ ] C.Hom[ X i , Y j ])
  -- foo {I} {J} {X} {Y} =
  --   Fam [ (I , X) , (J , Y) ] ≡⟨⟩
  --   (Σ[ f ∈ (⟨ I ⟩ → ⟨ J ⟩) ] (∀ i → C.Hom[ X i , Y (f i) ])) ≡⟨ sym $ ua Σ-Π-≃ ⟩
  --   ((i : ⟨ I ⟩) → Σ[ j ∈ ⟨ J ⟩ ] C.Hom[ X i , Y j ]) ∎

module BinProduct {ℓCo ℓCh} {ℓDo ℓDh} (C : Category ℓCo ℓCh) (bp : BinProducts' C) (D : Categoryᴰ C ℓDo ℓDh) (bpᴰ : BPᴰ.LiftedBinProducts D bp) where
  open BP.BinProduct

  private module C = BP.BinProducts'Notation {C = C} bp
  
  ∫CBinProducts : BinProducts' (∫C {C = C} D)
  ∫CBinProducts (xᶜ , xᴰ) = {! !}

module FamBinProducts {ℓ} (C : Category ℓ ℓ) (bp : BinProducts C) where
  private
    module C = BP.Notation C bp
    ΠC = Fam ℓ C
    module ΠC = Category ΠC

  module _ (x@(J , xⱼ) y@(K , yₖ) : ΠC.ob) where
    private
      X×Y : ΠC.ob
      X×Y .fst = J HSet.×Set K
      X×Y .snd (j , k) = xⱼ j C.× yₖ k
    
    _×Π_ = X×Y

  module _ {x y : ΠC.ob} where
    π₁ : ΠC [ x ×Π y , x ]
    π₁ .fst = fst
    π₁ .snd (j , k) = C.π₁

    π₂ : ΠC [ x ×Π y , y ]
    π₂ .fst = snd
    π₂ .snd (j , k) = C.π₂

    _,Π_ : ∀ {z : ΠC.ob} (f₁ : ΠC [ z , x ]) (f₂ : ΠC [ z , y ]) → ΠC [ z , x ×Π y ]
    ((f₁ , φ₁) ,Π (f₂ , φ₂)) .fst = λ k → f₁ k , f₂ k
    ((f₁ , φ₁) ,Π (f₂ , φ₂)) .snd k = (φ₁ k) C.,p (φ₂ k)

    -- UP : ∀ {z : ΠC.ob} (f₁ : ΠC [ z , x ]) (f₂ : ΠC [ z , y ]) → ∃![ f ∈ ΠC [ z , x ×Π y ] ] (f ⋆⟨ ΠC ⟩ π₁ ≡ f₁) × (f ⋆⟨ ΠC ⟩ π₂ ≡ f₂)
    -- UP f₁ f₂ .fst = f₁ ,Π f₂ , {! !} , {! !}
    -- UP f₁ f₂ .snd = {! !}

  open BP.BinProduct

  FamBinProducts : BinProducts (Fam ℓ C)
  FamBinProducts x y .binProdOb = x ×Π y
  FamBinProducts x y .binProdPr₁ = π₁ {x} {y}
  FamBinProducts x y .binProdPr₂ = π₂ {x} {y}
  FamBinProducts x y .univProp = {! UP !}

-- NOTE: C needs to have arbitrary products!
module FamExponentials {ℓ} (C : Category ℓ ℓ) (bp : BinProducts C) (exp : Exponentials C bp) where
  private
    module C where
      open Category C public
      open BP.Notation C bp public
      open Exp.ExpNotation C bp exp public

    ΠC = Fam ℓ C

    module Πbp = FamBinProducts C bp

    module ΠC where
      open Category ΠC public
      open BP.Notation ΠC Πbp.FamBinProducts public

  open import Cubical.Categories.Presheaf.Representable using (UniversalElement)
  open HSet using (_×Set_ ; _→Set_)

  _⇒Π_ : (x y : ΠC.ob) → ΠC.ob
  ((J , Xⱼ) ⇒Π (K , Yₖ)) .fst = J →Set K
  ((J , Xⱼ) ⇒Π (K , Yₖ)) .snd f = {! !} -- λ (j , k) → Xⱼ j C.⇒ Yₖ k

  FamExponentialIso : ∀ {x y z} → Iso (ΠC.Hom[ x ΠC.× y , z ]) (ΠC.Hom[ x , y ⇒Π z ])
  FamExponentialIso {x@(I , X)} {y@(J , Y)} {z@(K , Z)} =
    (ΠC.Hom[ x ΠC.× y , z ]) Iso⟨ Iso.idIso ⟩
    (Σ[ f ∈ (⟨ I ⟩ × ⟨ J ⟩ → ⟨ K ⟩) ] (∀ i,j → C.Hom[ (X (i,j .fst)) C.× (Y (i,j .snd)) , (Z (f i,j)) ])) Iso⟨ Σ-cong-iso-snd {! !} ⟩
    (Σ[ f ∈ (⟨ I ⟩ × ⟨ J ⟩ → ⟨ K ⟩) ] (∀ i,j → C.Hom[ (X (i,j .fst)) , (Y (i,j .snd)) C.⇒ (Z (f i,j)) ])) Iso⟨ {! !} ⟩
    (∀ i,j → Σ[ k ∈ ⟨ K ⟩ ] (C.Hom[ X (i,j .fst) , Y (i,j .snd) C.⇒ Z k ])) Iso⟨ {! !} ⟩
    (∀ i j → Σ[ k ∈ ⟨ K ⟩ ] (C.Hom[ X i , Y j C.⇒ Z k ])) Iso⟨ {! !} ⟩

    (∀ i → Σ[ f ∈ (⟨ J ⟩ → ⟨ K ⟩) ] (∀ j → C.Hom[ X i , Y j C.⇒ Z (f j) ])) Iso⟨ {! !} ⟩
    (∀ i → Σ[ f ∈ (⟨ J ⟩ → ⟨ K ⟩) ] (C.Hom[ X i , ((J , Y) ⇒Π (K , Z)) .snd f ])) Iso⟨ {! !} ⟩

    (Σ[ f ∈ (⟨ I ⟩ → ⟨ J ⟩ → ⟨ K ⟩) ] (∀ i → C.Hom[ X i , ((J , Y) ⇒Π (K , Z)) .snd (f i) ])) Iso⟨ Iso.idIso ⟩
    (ΠC.Hom[ x , y ⇒Π z ]) Iso∎

  FamExponentials : Exponentials (Fam ℓ C) Πbp.FamBinProducts
  FamExponentials (x , y) = ue where
    ue : UniversalElement _ _
    ue .UniversalElement.vertex = x ⇒Π y
    ue .UniversalElement.element = (λ { x₁ → {! !} }) , {! !}
    ue .UniversalElement.universal = {! !}
    -}

module DisplayedOverContr {ℓo ℓh ℓoᴰ ℓhᴰ} (C : Category ℓo ℓh) (Cᴰ : Categoryᴰ C ℓoᴰ ℓhᴰ)
  (contr-ob : isContr (C .Category.ob))
  where

  private
    x₀ = contr-ob .fst

    contr-x₀ : ∀ x → x₀ ≡ x
    contr-x₀ = contr-ob .snd

    contr′-x₀ : ∀ {x} → x ≡ x₀
    contr′-x₀ = sym $ contr-x₀ _

    module C = Category C
    E = C.Hom[ x₀ , x₀ ]
    module Cᴰ = Categoryᴰ Cᴰ

    ob-elim : ∀ {ℓ} {B : C.ob → Type ℓ} → (b₀ : B x₀) → ∀ x → B x
    ob-elim {B} b₀ x = subst B (contr-x₀ x) b₀

    ob-elim2 : ∀ {ℓ} {B : (x x′ : C.ob) → Type ℓ} → (b₀ : B x₀ x₀) → ∀ x x′ → B x x′
    ob-elim2 {B} b₀ x x′ = subst2 B (contr-x₀ x) (contr-x₀ x′) b₀

  ∫ᶜ : Category ℓoᴰ (ℓ-max ℓh ℓhᴰ)
  ∫ᶜ .Category.ob = Cᴰ.ob[ x₀ ]
  ∫ᶜ .Category.Hom[_,_] x y = Σ[ e ∈ E ] Cᴰ.Hom[ e ][ x , y ]
  ∫ᶜ .Category.id .fst = C.id
  ∫ᶜ .Category.id .snd = Cᴰ.idᴰ
  ∫ᶜ .Category._⋆_ (e₁ , fᴰ) (e₂ , gᴰ) .fst = e₁ C.⋆ e₂
  ∫ᶜ .Category._⋆_ (e₁ , fᴰ) (e₂ , gᴰ) .snd = fᴰ Cᴰ.⋆ᴰ gᴰ
  ∫ᶜ .Category.⋆IdL (e , fᴰ) i .fst = C.⋆IdL e i
  ∫ᶜ .Category.⋆IdL (e , fᴰ) i .snd = Cᴰ.⋆IdLᴰ fᴰ i
  ∫ᶜ .Category.⋆IdR (e , fᴰ) i .fst = C.⋆IdR e i
  ∫ᶜ .Category.⋆IdR (e , fᴰ) i .snd = Cᴰ.⋆IdRᴰ fᴰ i
  ∫ᶜ .Category.⋆Assoc (e₁ , fᴰ) (e₂ , gᴰ) (e₃ , hᴰ) i .fst = C.⋆Assoc e₁ e₂ e₃ i
  ∫ᶜ .Category.⋆Assoc (e₁ , fᴰ) (e₂ , gᴰ) (e₃ , hᴰ) i .snd = Cᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ i
  ∫ᶜ .Category.isSetHom = isSetΣ C.isSetHom λ _ → Cᴰ.isSetHomᴰ

  open Functor

  ∫ᶜ→∫C : Functor ∫ᶜ (∫C Cᴰ)
  ∫ᶜ→∫C .F-ob xᴰ = x₀ , xᴰ
  ∫ᶜ→∫C .F-hom (e , fᴰ) = e , fᴰ
  ∫ᶜ→∫C .F-id = refl
  ∫ᶜ→∫C .F-seq (e₁ , fᴰ) (e₂ , gᴰ) = refl

  ∫C→∫ᶜ : Functor (∫C Cᴰ) ∫ᶜ
  ∫C→∫ᶜ .F-ob = uncurry $ ob-elim (id _)
  ∫C→∫ᶜ .F-hom = goal _ _ _ _ where
    goal : (x y : C.ob) → (xᴰ : Cᴰ.ob[ x ]) (yᴰ : Cᴰ.ob[ y ])
      → (f : (∫C Cᴰ) [ (x , xᴰ) , (y , yᴰ) ])
      → ∫ᶜ [ ∫C→∫ᶜ .F-ob (x , xᴰ) , ∫C→∫ᶜ .F-ob (y , yᴰ) ]
    goal = ob-elim2 λ xᴰ yᴰ (e , f) → e , {! !}
  ∫C→∫ᶜ .F-id = {! !}
  ∫C→∫ᶜ .F-seq = {! !}

  ∫ᶜ-equiv : ∫ᶜ ≃ᶜ ∫C {C = C} Cᴰ
  ∫ᶜ-equiv = AdjointEquivalence.to≃ᶜ {! !}
