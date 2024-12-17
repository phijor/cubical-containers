open import GpdCont.Prelude hiding (J)
open import Cubical.Categories.Category.Base using (Category ; _[_,_])

module GpdCont.Categories.Family (ℓ : Level) {ℓo ℓh} (C : Category ℓo ℓh) where

open import GpdCont.Univalence
open import GpdCont.HomotopySet

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

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
