{-# OPTIONS --lossy-unification #-}
open import GpdCont.Prelude hiding (J)
open import Cubical.Categories.Category.Base

module GpdCont.Categories.Family (ℓ : Level) {ℓo ℓh} (C : Category ℓo ℓh) where

open import GpdCont.Univalence
open import GpdCont.HomotopySet
import      GpdCont.Categories.Products as Pr
import      GpdCont.Categories.Diagonal as Diagonal
import GpdCont.Categories.Fiber as Fiber

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (domIsoDep)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Sum

open import Cubical.Categories.Category.Path
open import Cubical.Categories.Instances.Sets using (SET ; isUnivalentSET)
open import Cubical.Categories.Constructions.TotalCategory.Base using (∫C)
open import Cubical.Categories.Displayed.Base as Disp using (Categoryᴰ)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.BinProduct.More


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

  uaFam : ∀ {x@(J , X) y@(K , Y) : Category.ob Fam}
    → (e : ⟨ J ⟩ ≃ ⟨ K ⟩)
    → (eᴰ : ∀ j → X j ≡ Y (equivFun e j)) → x ≡ y
  uaFam e q = Fam≡ (hSet≡ (ua e)) (ua→ q)

  FamHom≡ : ∀ {X Y} {f×φ@(f , φ) g×ψ@(g , ψ) : Fam [ X , Y ]}
    → (p : f ≡ g)
    → (∀ j → PathP (λ i → C [ X .snd j , Y .snd (p i j) ]) (φ j) (ψ j))
    → f×φ ≡ g×ψ
  FamHom≡ p q i .fst = p i
  FamHom≡ p q i .snd j = q j i

  FamIsoOverId : ∀ {X} {c d : ⟨ X ⟩ → C.ob} (f : ∀ j → CatIso C (c j) (d j)) → CatIso Fam (X , c) (X , d)
  FamIsoOverId f .fst = (id _ , fst ∘ f)
  FamIsoOverId f .snd .isIso.inv = (id _ , isIso.inv ∘ snd ∘ f)
  FamIsoOverId f .snd .isIso.sec i = id _ , λ j → (isIso.sec $ snd $ f j) i
  FamIsoOverId f .snd .isIso.ret i = id _ , λ j → (isIso.ret $ snd $ f j) i

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

module Univalent (is-univalent : isUnivalent C) where
  private
    module C where
      open Category C public
      open isUnivalent is-univalent public

    open Fiber (SET ℓ) Famᴰ

    fiber-cat-path : ∀ J → FiberCategory J ≡ Diagonal.ΠC C _ J
    fiber-cat-path J = CategoryPath.mk≡ path where
      path : CategoryPath _ _
      path .CategoryPath.ob≡ = refl
      path .CategoryPath.Hom≡ = refl
      path .CategoryPath.id≡ = refl
      path .CategoryPath.⋆≡ i f g = transportRefl (λ j → f j C.⋆ g j) i

    is-univalent-Diagonal : ∀ J → isUnivalent (Diagonal.ΠC C ℓ J)
    is-univalent-Diagonal = Diagonal.isUnivalentΠ C _ is-univalent

  isUnivalentFam : isUnivalent Fam
  isUnivalentFam = isUnivalentFiber→isUnivalentTotalCategory isUnivalentSET univ-fam-fiber where
    univ-fam-fiber : (J : hSet ℓ) → isUnivalent (FiberCategory J)
    univ-fam-fiber J = subst isUnivalent (sym (fiber-cat-path J)) (is-univalent-Diagonal J)

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
      univ-iso .Iso.sec g = funExt λ k → FamHom≡ refl (λ j → C.⋆IdL (g k .snd j))
      univ-iso .Iso.ret f = FamHom≡ refl λ kj → C.⋆IdL (f .snd kj)

      is-univ : isEquiv (univ-iso .Iso.fun)
      is-univ = isoToIsEquiv univ-iso

    FamCoproduct : Coproduct K c
    FamCoproduct .UniversalElement.vertex = coprod
    FamCoproduct .UniversalElement.element = inj
    FamCoproduct .UniversalElement.universal = is-univ

  FamCoproducts : Coproducts
  FamCoproducts = FamCoproduct

module BinProducts (p : BinProducts C) where
  private
    module C where
      open Category C public
      open BinProductsNotation p public

  module _ (x y : Fam.ob) where
    x×y : Fam.ob
    x×y .fst = Index x ×Set Index y
    x×y .snd (j , k) = El x j C.× El y k

    π : Fam [ x×y , x ] × Fam [ x×y , y ]
    π .fst = fst , λ _ → C.π₁
    π .snd = snd , λ _ → C.π₂

    univ : (z : Fam.ob) → Fam [ z , x×y ] → Fam [ z , x ] × Fam [ z , y ]
    univ z f .fst = f Fam.⋆ π .fst
    univ z f .snd = f Fam.⋆ π .snd

    univ-iso : ∀ z → Iso (Fam [ z , x×y ]) (Fam [ z , x ] × Fam [ z , y ])
    univ-iso z =
      -- Σ[ φ ∈ (⟨ Index z ⟩ → ⟨ Index x ⟩ × ⟨ Index y ⟩) ] (∀ k → C [ El z k , El x (φ k .fst) C.× El y (φ k .snd) ])
      --   Iso⟨ invIso Σ-Π-Iso ⟩
      -- ((k : ⟨ Index z ⟩) → Σ[ (i , j) ∈ ⟨ Index x ⟩ × ⟨ Index y ⟩ ] C [ El z k , El x i C.× El y j ])
      --   Iso⟨ codomainIsoDep (λ k → Σ-cong-iso-snd λ (i , j) → C.×ue.universalIso (El x i) (El y j) (El z k)) ⟩
      -- ((k : ⟨ Index z ⟩) → Σ[ (i , j) ∈ ⟨ Index x ⟩ × ⟨ Index y ⟩ ] C.Hom[ El z k , El x i ] × C.Hom[ El z k , El y j ])
      --   Iso⟨ {! C.×ue.universalIso !} ⟩
      -- (Σ[ φ ∈ (⟨ Index z ⟩ → ⟨ Index x ⟩) ] (∀ k → C.Hom[ El z k , El x (φ k) ])) × (Σ[ ψ ∈ (⟨ Index z ⟩ → ⟨ Index y ⟩) ] (∀ k → C.Hom[ El z k , El y (ψ k) ]))
      --   ∎Iso
      Σ[ φ ∈ (⟨ Index z ⟩ → ⟨ Index x ⟩ × ⟨ Index y ⟩) ] (∀ k → C [ El z k , El x (φ k .fst) C.× El y (φ k .snd) ])
        Iso⟨ Σ-cong-iso-snd (λ φ → codomainIsoDep λ k → C.×ue.universalIso (El x _) (El y _) (El z _)) ⟩
      Σ[ φ ∈ (⟨ Index z ⟩ → ⟨ Index x ⟩ × ⟨ Index y ⟩) ] (∀ k → C [ El z k , El x _ ] × C [ El z k , El y _ ])
        Iso⟨ shuffle ⟩
      (Σ[ φ ∈ (⟨ Index z ⟩ → ⟨ Index x ⟩) ] (∀ k → C.Hom[ El z k , El x (φ k) ])) × (Σ[ ψ ∈ (⟨ Index z ⟩ → ⟨ Index y ⟩) ] (∀ k → C.Hom[ El z k , El y (ψ k) ]))
        ∎Iso
        where
          shuffle : Iso (Σ _ _) ((Σ _ _) × (Σ _ _))
          shuffle .Iso.fun (φ , f) .fst .fst = fst ∘ φ
          shuffle .Iso.fun (φ , f) .fst .snd = fst ∘ f
          shuffle .Iso.fun (φ , f) .snd .fst = snd ∘ φ
          shuffle .Iso.fun (φ , f) .snd .snd = snd ∘ f
          shuffle .Iso.inv ((φ , f) , ψ , g) .fst k = φ k , ψ k
          shuffle .Iso.inv ((φ , f) , ψ , g) .snd k = f k , g k
          shuffle .Iso.sec _ = refl
          shuffle .Iso.ret _ = refl


    intro : (z : Fam.ob) → Fam [ z , x ] × Fam [ z , y ] → Fam [ z , x×y ]
    intro z (g₁ , g₂) .fst k = HomIndex g₁ k , HomIndex g₂ k
    intro z (g₁ , g₂) .snd k = HomEl g₁ k C.,p HomEl g₂ k

    is-equiv-univ : ∀ z → isEquiv (univ z)
    is-equiv-univ z = isoToIsEquiv (univ-iso z)

    bp : BinProduct Fam (x , y)
    bp .UniversalElement.vertex = x×y
    bp .UniversalElement.element = π
    bp .UniversalElement.universal = is-equiv-univ

  famBinProducts : BinProducts Fam
  famBinProducts = uncurry bp


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

    univ : (x : Fam.ob) → isEquiv (λ f k → f Fam.⋆ proj k)
    univ = isoToIsEquiv ∘ univ-iso

    FamProduct : Product K c
    FamProduct .UniversalElement.vertex = prod
    FamProduct .UniversalElement.element = proj
    FamProduct .UniversalElement.universal = univ

  FamProducts : Products
  FamProducts = FamProduct

module Exponentials where
  open import Cubical.Categories.Exponentials
  open import Cubical.Data.Empty

  private
    module _ (bp : BinProducts C) (exp : AllExponentiable C bp) where
      module C where
        open Category C public
        open BinProductsNotation bp public
        open ExponentialsNotation bp exp public

      emb : C.ob → Fam.ob
      emb Y .fst = UnitSet _
      emb Y .snd = λ _ → Y

      module Fam× where
        open BinProductsNotation (BinProducts.famBinProducts bp) public

        bpw : ∀ x → BinProductsWith Fam x
        bpw x = BinProducts→BinProductsWith _ x (BinProducts.famBinProducts bp)

      konst-exp : (X : C.ob) → (y : Fam.ob) → Exponential Fam (emb X) y (Fam×.bpw (emb X))
      konst-exp X y@(J , Y) = goal where
        [X,y] : Fam.ob
        [X,y] .fst = J
        [X,y] .snd j = X C.⇒ Y j

        ev : Fam [ [X,y] Fam×.× (emb X) , y ]
        ev .fst = fst
        ev .snd (j , _) = C.⇒ue.element X (Y j)

        univ-iso : (z : Fam.ob) → Iso (Fam [ z , [X,y] ]) (Fam [ z Fam×.× emb X , y ])
        univ-iso z =
          Σ[ φ ∈ (⟨ Index z ⟩ → ⟨ J ⟩) ] (∀ k → C [ El z k , X C.⇒ Y (φ k) ])
            Iso⟨ Σ-cong-iso-snd (λ φ → codomainIsoDep λ k → C.⇒ue.universalIso X (Y (φ k)) (El z k)) ⟩
          Σ[ φ ∈ (⟨ Index z ⟩ → ⟨ J ⟩) ] (∀ k → C.Hom[ El z k C.× X , Y (φ k) ])
            Iso⟨ Σ-cong-iso (domIso (invIso rUnit*×Iso)) (λ φ → domIsoDep rUnit*×Iso) ⟩
          Σ[ φ ∈ (⟨ Index z ⟩ × _ → ⟨ J ⟩) ] (∀ k → C.Hom[ (El z (k .fst)) C.× X , Y (φ k) ])
            ∎Iso

        goal : Exponential Fam (emb X) y _
        goal .UniversalElement.vertex = [X,y]
        goal .UniversalElement.element = ev
        goal .UniversalElement.universal z = isoToIsEquiv (univ-iso z)

      exp' : (ip : Pr.Products C ℓ) → (x y : Fam.ob) → Exponential Fam x y (Fam×.bpw x)
      exp' ip x y = goal where

        module CΠ = Pr.Notation C _ ip

        module FamΠ where
          open Pr.Notation Fam ℓ (Products.FamProducts ip) public

        module [xᵢ,y] (ix : ⟨ Index x ⟩) where
          open ExponentialNotation (Fam×.bpw (emb (El x ix))) (konst-exp (El x ix) y) public

        [x,y] : Fam.ob
        [x,y] = FamΠ.Π (Index x) [xᵢ,y].vert

        ev : Fam [ [x,y] Fam×.× x , y ]
        ev .fst (φ , ix) = φ ix
        ev .snd (φ , ix) = (CΠ.π (Index x) _ ix C.×p C.id {x = El x ix}) C.⋆ HomEl ([xᵢ,y].app ix) (φ ix , tt*)

        univ-iso : ∀ z → Iso (Fam [ z , [x,y] ]) (Fam [ z Fam×.× x , y ])
        univ-iso z =
          Fam [ z , FamΠ.Π _ _ ]
            Iso⟨ FamΠ.univ-iso (Index x) _ z ⟩
          (∀ ix → Fam [ z , [xᵢ,y].vert ix ])
            Iso⟨ codomainIsoDep (λ ix → [xᵢ,y].⇒ue.universalIso ix z) ⟩
          (∀ ix → Fam [ z Fam×.× emb (El x ix) , y ])
            Iso⟨ Σ-Π-Iso ⟩
          Σ[ φ ∈ (⟨ Index x ⟩ → ⟨ Index z ⟩ × Unit* → ⟨ Index y ⟩) ] _
            Iso⟨ iso
              (λ (φ , f) → (λ (k , i) → φ i (k , _)) , (λ (k , i) → f i (k , tt*)))
              (λ (φ , f) → (λ i (k , _) → φ (k , i)) , (λ i (x , _) → f (x , i)))
              (λ _ → refl)
              (λ _ → refl)
            ⟩
          Σ[ φ ∈ (⟨ Index z ⟩ × ⟨ Index x ⟩ → ⟨ Index y ⟩) ] _
            ∎Iso

        goal : Exponential Fam x y (Fam×.bpw x)
        goal .UniversalElement.vertex = [x,y]
        goal .UniversalElement.element = ev
        goal .UniversalElement.universal z = subst isEquiv coh $ isoToIsEquiv (univ-iso z) where
          coh : Iso.fun (univ-iso z) ≡ (λ f → ({! !} Fam×.,p {! !}) Fam.⋆ ev)
          coh = funExt λ f → FamHom≡ refl λ where
            (k , i) → {! !}
