open import GpdCont.Prelude hiding (J)
open import Cubical.Categories.Category.Base using (Category ; _[_,_])

module GpdCont.Categories.Family (ℓ : Level) {ℓo ℓh} (C : Category ℓo ℓh) where

open import GpdCont.Univalence
open import GpdCont.HomotopySet
import      GpdCont.Categories.Products as Pr

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (domIsoDep)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Constructions.TotalCategory.Base using (∫C)
open import Cubical.Categories.Displayed.Base as Disp using (Categoryᴰ)
open import Cubical.Categories.Presheaf.Representable


module _ where
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
  FamHom≡ p q i .fst = p i
  FamHom≡ p q i .snd j = q j i

private
  module Fam = Category Fam

module Notation where
  private
    module C = Category C

  Index : Fam.ob → hSet ℓ
  Index = fst

  El : (x : Fam.ob) → ⟨ Index x ⟩ → C.ob
  El = snd

  HomIndex : {x y : Fam.ob} → Fam.Hom[ x , y ] → ⟨ Index x ⟩ → ⟨ Index y ⟩
  HomIndex = fst

  HomEl : {x y : Fam.ob} → (f : Fam.Hom[ x , y ]) → (j : ⟨ Index x ⟩) → C.Hom[ El x j , El y (HomIndex f j) ]
  HomEl = snd

open Notation


module Coproducts where
  open import GpdCont.Categories.Coproducts Fam ℓ as FamCoproduct

  private
    module C = Category C

  module _ (K : hSet ℓ) (c : ⟨ K ⟩ → Fam.ob) where
    coprod : Fam.ob
    coprod .fst = ΣSet K (Index ∘ c)
    coprod .snd = uncurry (El ∘ c)

    inj : (k : ⟨ K ⟩) → Σ[ f ∈ (⟨ Index (c k) ⟩ → Σ[ k ∈ ⟨ K ⟩ ] ⟨ Index (c k) ⟩) ] ∀ j → C.Hom[ El (c k) j , El (c (f j .fst)) (f j .snd) ]
    inj k .fst j = k , j
    inj k .snd j = C.id {x = El (c k) j}

    module _ (y : Fam.ob) where
      univ-iso : Iso Fam.Hom[ coprod , y ] ((k : ⟨ K ⟩) → Fam.Hom[ c k , y ])
      univ-iso .Iso.fun f = λ k → inj k Fam.⋆ f
      univ-iso .Iso.inv g .fst (k , j) = g k .fst j
      univ-iso .Iso.inv g .snd (k , j) = g k .snd j
      univ-iso .Iso.rightInv g = funExt λ k → FamHom≡ refl (λ j → C.⋆IdL (g k .snd j))
      univ-iso .Iso.leftInv f = FamHom≡ refl λ kj → C.⋆IdL (f .snd kj)

      is-univ : isEquiv (univ-iso .Iso.fun)
      is-univ = isoToIsEquiv univ-iso

    FamCoproduct : Coproduct K c
    FamCoproduct .UniversalElement.vertex = coprod
    FamCoproduct .UniversalElement.element = inj
    FamCoproduct .UniversalElement.universal = is-univ

  FamCoproducts : Coproducts
  FamCoproducts = FamCoproduct

module Products (p : Pr.Products C ℓ) where

  private
    open module FamProduct = Pr Fam ℓ
    module C where
      open Category C public
      open Pr.Notation C ℓ p public


  module _ (K : hSet ℓ) (c : ⟨ K ⟩ → Fam.ob) where
    private
      c′ : (φ : ∀ k → ⟨ Index (c k) ⟩) (k : ⟨ K ⟩) → C.ob
      c′ φ k = El (c k) (φ k)

    prod : Fam.ob
    prod .fst = ΠSet {S = ⟨ K ⟩} λ k → Index (c k)
    prod .snd = λ (φ : ∀ k → ⟨ Index (c k) ⟩) → C.Π K (c′ φ)

    proj : (k : ⟨ K ⟩) → Fam.Hom[ prod , c k ]
    proj k .fst φ = φ k
    proj k .snd φ = C.π K (c′ φ) k

    univ-iso : ∀ (x : Fam.ob) → Iso Fam.Hom[ x , prod ] ((k : ⟨ K ⟩) → Fam.Hom[ x , c k ])
    univ-iso x =
      Fam.Hom[ x , prod ]
        Iso⟨⟩
      Σ[ φ ∈ (⟨ Index x ⟩ → (k : ⟨ K ⟩) → ⟨ Index (c k) ⟩) ] ((j : ⟨ Index x ⟩) → C.Hom[ El x j , C.Π K (c′ (φ j)) ])
        Iso⟨ invIso Σ-Π-Iso ⟩
      ((j : ⟨ Index x ⟩) → Σ[ φ ∈ ((k : ⟨ K ⟩) → ⟨ Index (c k) ⟩) ] (C.Hom[ El x j , C.Π K (c′ φ) ]))
        Iso⟨ codomainIsoDep (λ j → Σ-cong-iso-snd λ φ → C.univ-iso K (c′ φ) (El x j)) ⟩
      ((j : ⟨ Index x ⟩) → Σ[ φ ∈ ((k : ⟨ K ⟩) → ⟨ Index (c k) ⟩) ] ((k : ⟨ K ⟩) → C.Hom[ El x j , c′ φ k ]))
        Iso⟨ codomainIsoDep (λ j → invIso Σ-Π-Iso) ⟩
      ((j : ⟨ Index x ⟩) → (k : ⟨ K ⟩) → Σ[ i ∈ ⟨ Index (c k) ⟩ ] (C.Hom[ El x j , El (c k) i ]))
        Iso⟨ flipIso ⟩
      ((k : ⟨ K ⟩) → (j : ⟨ Index x ⟩) → Σ[ i ∈ ⟨ Index (c k) ⟩ ] (C.Hom[ El x j , El (c k) i ]))
        Iso⟨ codomainIsoDep (λ k → Σ-Π-Iso) ⟩
      ((k : ⟨ K ⟩) → Σ[ φ ∈ ((j : ⟨ Index x ⟩) → ⟨ Index (c k) ⟩) ] (∀ j → C.Hom[ El x j , El (c k) (φ j) ]))
        Iso⟨⟩
      ((k : ⟨ K ⟩) → Fam.Hom[ x , c k ]) ∎Iso

    univ : (x : Fam.ob) → isEquiv (univ-iso x .Iso.fun)
    univ = isoToIsEquiv ∘ univ-iso

    FamProduct : Product K c
    FamProduct .UniversalElement.vertex = prod
    FamProduct .UniversalElement.element = proj
    FamProduct .UniversalElement.universal = univ

  FamProducts : Products
  FamProducts = FamProduct

module ConstantExponentials (p : Pr.Products C ℓ) where
  open import GpdCont.Bool
  open import Cubical.Categories.Exponentials using (Exponential)

  private
    open module FamProduct = Pr Fam ℓ
    module C where
      open Category C public
      open Pr.Notation C ℓ p public

    famBinProducts = Pr.Products→BinProducts Fam ℓ (Products.FamProducts p)
    module ΠFam = FamProduct.Notation (Products.FamProducts p)

  konst : hSet ℓ → Fam.ob
  konst K .fst = K
  konst K .snd = const C.terminal

  [konst_,_]' : (K : hSet ℓ) (c : Fam.ob) → Fam.ob
  [konst K , c ]' = ΠFam.Π K (const c)

  [konst_,_] : (K : hSet ℓ) (c : Fam.ob) → Fam.ob
  [konst K , c ] .fst = K →Set (Index c)
  [konst K , c ] .snd f = C.Π K (El c ∘ f)

  module _ (K : hSet ℓ) (c : Fam.ob) where
    ap-idx : ⟨ Index (konst K ΠFam.× [konst K , c ]) ⟩ → ⟨ Index c ⟩
    ap-idx = ap ∘ bool-unelim where
      ap : ⟨ K ⟩ × ⟨ K →Set (Index c) ⟩ → ⟨ Index c ⟩
      ap (k , f) = f k

    eval₀ : Fam.Hom[ (konst K) ΠFam.× [konst K , c ] , [konst K , c ] ]
    eval₀ = ΠFam.π₂

    eval-El : ∀ (f : ⟨ K ⟩ → ⟨ Index c ⟩) k → C.Hom[ El [konst K , c ] f , El c (f k) ]
    eval-El f = C.π K (El c ∘ f)

    module eval' (k : ⟨ K ⟩) (f : ⟨ K ⟩ → ⟨ Index c ⟩) where
      index : ⟨ Index c ⟩
      index = f k

      el' : C.Hom[ C._×_ {! !} {! !} , El c index ]
      el' = {! !}

      el : C.Hom[ El (konst K ΠFam.× [konst K , c ]') (bool-elim k f) , El c index ]
      el = {! !} C.⋆ eval-El f k

      -- hom : Σ[ j ∈ ⟨ Index c ⟩ ] C.Hom[ El (konst K ΠFam.× [konst K , c ]') (bool-elim k f) , El c j ]
      -- hom .fst = index
      -- hom .snd = el

    module eval (idx : ⟨ Index ((konst K) ΠFam.× [konst K , c ]') ⟩) where
      open Σ (bool-unelim idx) renaming (fst to k ; snd to f)

      index : ⟨ Index c ⟩
      index = f k

      el' : C.Hom[ {! !} C.× {! !}, El c index ]
      el' = {! !}
      el : C.Hom[ El (konst K ΠFam.× [konst K , c ]') idx , El c index ]
      el = {! !} C.⋆ eval-El f k

      hom : Σ[ j ∈ ⟨ Index c ⟩ ] C.Hom[ El (konst K ΠFam.× [konst K , c ]') idx , El c j ]
      hom .fst = index
      hom .snd = el

    eval' : Fam.Hom[ (konst K) ΠFam.× [konst K , c ]' , c ]
    eval' = Iso.fun Σ-Π-Iso eval.hom

    eval : Fam.Hom[ (konst K) ΠFam.× [konst K , c ] , c ]
    eval .fst = ap-idx
    eval .snd idx using (k , f) ← bool-unelim idx = goal where
      goal : C.Hom[ El (konst K ΠFam.× [konst K , c ]) idx , El c (f k) ]
      goal = HomEl eval₀ idx C.⋆ eval-El f k

    univ-iso' : ∀ x → Iso (Fam [ x , [konst K , c ] ]) (Fam [ konst K ΠFam.× x , c ])
    univ-iso' x =
      Σ[ f ∈ (⟨ Index x ⟩ → ⟨ K ⟩ → ⟨ Index c ⟩) ]
        ((idx : ⟨ Index x ⟩) → C.Hom[ El x idx , El [konst K , c ] (f idx) ])
        Iso⟨ invIso Σ-Π-Iso ⟩
      ((j : ⟨ Index x ⟩)
        → Σ[ ic ∈ (⟨ K ⟩ → ⟨ Index c ⟩) ] C.Hom[ El x j , El [konst K , c ] ic ])
        Iso⟨ codomainIsoDep (λ j → Σ-cong-iso-snd λ ic → C.univ-iso K _ (El x j)) ⟩
      ((j : ⟨ Index x ⟩)
        → Σ[ ic ∈ (⟨ K ⟩ → ⟨ Index c ⟩) ] ∀ k → C.Hom[ El x j , El c (ic k) ])
        Iso⟨ codomainIsoDep (λ j → invIso Σ-Π-Iso) ⟩
      ((j : ⟨ Index x ⟩) (k : ⟨ K ⟩)
        → Σ[ ic ∈ ⟨ Index c ⟩ ] C.Hom[ El x j , El c ic ])
        Iso⟨ invIso curryIso ⟩
      ((idx : ⟨ Index x ⟩ × ⟨ K ⟩)
        → Σ[ ic ∈ ⟨ Index c ⟩ ] C.Hom[ El x (idx .fst) , El c ic ])
        Iso⟨ codomainIsoDep (λ { idx@(j , k) → Σ-cong-iso-snd (el-iso j k)} ) ⟩
      ((idx : ⟨ Index x ⟩ × ⟨ K ⟩)
        → Σ[ ic ∈ ⟨ Index c ⟩ ] C.Hom[ El (konst K ΠFam.× x) (Iso.fun index-iso' idx) , El c ic ])
        Iso⟨ invIso (domIsoDep index-iso') ⟩
      ((idx : ⟨ Index (konst K ΠFam.× x) ⟩)
        → Σ[ ic ∈ ⟨ Index c ⟩ ] C.Hom[ El (konst K ΠFam.× x) idx , El c ic ])
        Iso⟨ Σ-Π-Iso ⟩
      Σ[ f ∈ (⟨ Index (konst K ΠFam.× x) ⟩ → ⟨ Index c ⟩) ]
        ((idx : ⟨ Index (konst K ΠFam.× x) ⟩) → C.Hom[ El (konst K ΠFam.× x) idx , El c (f idx) ] )
        Iso⟨⟩
      Fam [ konst K ΠFam.× x , c ] Iso∎
      where
        index-iso' : Iso (⟨ Index x ⟩ × ⟨ K ⟩) (⟨ Index (konst K ΠFam.× x) ⟩)
        index-iso' =
          ⟨ Index x ⟩ × ⟨ Index (konst K) ⟩ Iso⟨ Σ-swap-Iso ⟩
          ⟨ Index (konst K) ⟩ × ⟨ Index x ⟩ Iso⟨ bool-elim-Iso ⟩
          (∀ b → ⟨ Index (bool-elim (konst K) x b) ⟩) Iso⟨⟩
          ⟨ Index (konst K ΠFam.× x) ⟩ Iso∎

        index-iso : Iso (⟨ Index x ⟩ → ⟨ K ⟩ → ⟨ Index c ⟩) (⟨ Index (konst K ΠFam.× x) ⟩ → ⟨ Index c ⟩)
        index-iso =
          (⟨ Index x ⟩ → ⟨ K ⟩ → ⟨ Index c ⟩) Iso⟨ invIso curryIso ⟩
          (⟨ Index x ⟩ × ⟨ Index (konst K) ⟩ → ⟨ Index c ⟩) Iso⟨ domIso Σ-swap-Iso ⟩
          (⟨ Index (konst K) ⟩ × ⟨ Index x ⟩ → ⟨ Index c ⟩) Iso⟨ domIso bool-elim-Iso ⟩
          ((∀ b → ⟨ Index (bool-elim (konst K) x b) ⟩) → ⟨ Index c ⟩) Iso⟨⟩
          (⟨ Index (konst K ΠFam.× x) ⟩ → ⟨ Index c ⟩) Iso∎

        el-iso : (j : ⟨ Index x ⟩) → (k : ⟨ K ⟩) → (ic : ⟨ Index c ⟩)
          → Iso
            C.Hom[ El x j , El c ic ]
            C.Hom[ El (konst K ΠFam.× x) (Iso.fun index-iso' (j , k)) , El c ic ]
        el-iso j k ic =
          C.Hom[ El x j , El c ic ] Iso⟨ {! !} ⟩
          C.Hom[ C.terminal C.× El x j , El c ic ] Iso⟨ {! !} ⟩
          C.Hom[ El (konst K ΠFam.× x) (Iso.fun index-iso' (j , k)) , El c ic ] Iso∎

    univ-iso : ∀ x → Iso (Fam [ x , [konst K , c ] ]) (Fam [ konst K ΠFam.× x , c ])
    univ-iso x .Iso.fun = λ f → (Fam.id {x = konst K} ΠFam.×p f) Fam.⋆ eval
    univ-iso x .Iso.inv g .fst = the (⟨ Index x ⟩ → ⟨ K ⟩ → ⟨ Index c ⟩) λ idx k → HomIndex g (bool-elim k idx)
    univ-iso x .Iso.inv g .snd idx = the
      (C.Hom[ El x idx , C.Π K (El c ∘ HomIndex g ∘ λ k → bool-elim k idx) ])
      (C.univ-iso K (El c ∘ (HomIndex g ∘ (λ k → bool-elim k idx))) (El x idx) .Iso.inv {!HomEl g!})
    univ-iso x .Iso.rightInv = {! !}
    univ-iso x .Iso.leftInv = {! !}

    univ-equiv : ∀ x → Fam [ x , [konst K , c ] ] ≃ Fam [ konst K ΠFam.× x , c ]
    univ-equiv x .fst = λ f → (Fam.id {x = konst K} ΠFam.×p f) Fam.⋆ eval
    univ-equiv x .snd = {! isoToIsEquiv (univ-iso x) !}

    ConstantExponential : Exponential Fam (konst K) c (famBinProducts (konst K))
    ConstantExponential .UniversalElement.vertex = [konst K , c ]
    ConstantExponential .UniversalElement.element = eval
    ConstantExponential .UniversalElement.universal x = subst isEquiv {! !} (equivIsEquiv (univ-equiv x))

{-

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
