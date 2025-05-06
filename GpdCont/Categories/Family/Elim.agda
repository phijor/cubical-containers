module GpdCont.Categories.Family.Elim where

open import GpdCont.Prelude
import      GpdCont.Categories.Family as Family
open import GpdCont.Categories.Functor using (isSplitEssentiallySurjective)
open import GpdCont.Categories.Coproducts using (Coproducts) renaming (module Notation to CoproductNotation)

open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism using (F-Iso)
open import Cubical.Categories.Equivalence.Base using (isEquivalence ; WeakInverse)
open import Cubical.Categories.Equivalence.Properties using (isFullyFaithful+isEquivF-ob→isEquiv)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
import      Cubical.HITs.PropositionalTruncation as PT

module Map {ℓ ℓo ℓh ℓo' ℓh'} {C : Category ℓo ℓh} {D : Category ℓo' ℓh'} (F : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F

    Fam[C] = Family.Fam ℓ C
    Fam[D] = Family.Fam ℓ D

    module Fam[C] = Category Fam[C]
    module Fam[D] = Category Fam[D]

  mapFunctor : Functor Fam[C] Fam[D]
  mapFunctor .Functor.F-ob (J , c) = J , F.F-ob ∘ c
  mapFunctor .Functor.F-hom (φ , f) = φ , F.F-hom ∘ f
  mapFunctor .Functor.F-id = ΣPathP (refl , funExt λ _ → F.F-id)
  mapFunctor .Functor.F-seq (φ , f) (γ , g) = ΣPathP (refl , funExt λ j → F.F-seq (f j) (g (φ j)))

  private
    Fam[F] = mapFunctor
    module Fam[F] = Functor Fam[F]

  isFullyFaithfulMap : F.isFullyFaithful → Fam[F].isFullyFaithful
  isFullyFaithfulMap is-ff x@(J , c) y@(K , d) = equivIsEquiv hom-equiv where
    hom-equivᴰ : (φ : ⟨ J ⟩ → ⟨ K ⟩) → (∀ j → C [ c j , d (φ j) ]) ≃ (∀ j → D [ F.F-ob (c j) , F.F-ob (d (φ j)) ])
    hom-equivᴰ φ = equivΠCod λ j → F.F-hom , is-ff (c j) (d (φ j))

    hom-equiv : Fam[C] [ x , y ] ≃ Fam[D] [ Fam[F] ⟅ x ⟆ , Fam[F] ⟅ y ⟆ ]
    hom-equiv = Σ-cong-equiv-snd hom-equivᴰ

  isSplitEssentiallySurjectiveMap : isSplitEssentiallySurjective F → isSplitEssentiallySurjective Fam[F]
  isSplitEssentiallySurjectiveMap is-split y@(K , d) = goal where
    goal-at : (k : ⟨ K ⟩) → Σ[ c ∈ C.ob ] CatIso D (F.F-ob c) (d k)
    goal-at = is-split ∘ d

    c : ⟨ K ⟩ → C.ob
    c = fst ∘ goal-at

    p : CatIso Fam[D] (K , F.F-ob ∘ c) (K , d)
    p = Family.FamIsoOverId ℓ D (snd ∘ goal-at)

    goal : Σ[ x ∈ Fam[C].ob ] CatIso Fam[D] (Fam[F] ⟅ x ⟆) y
    goal .fst .fst = K
    goal .fst .snd = c
    goal .snd = p

  isEquivObMap : isEquiv F.F-ob → isEquiv Fam[F].F-ob
  isEquivObMap is-equiv-F₀ = equivIsEquiv $ Σ-cong-equiv-snd λ J → equivΠCod λ j → F.F-ob , is-equiv-F₀

  isFullyFaithful×isEquivOb→isEquivMap : F.isFullyFaithful → isEquiv F.F-ob → isEquivalence Fam[F]
  isFullyFaithful×isEquivOb→isEquivMap is-ff is-equiv-F₀ = isFullyFaithful+isEquivF-ob→isEquiv
    (isFullyFaithfulMap is-ff)
    (isEquivObMap is-equiv-F₀)

open Map using () renaming (mapFunctor to Fam[_])

module _ {ℓ ℓo ℓh ℓo' ℓh'} {C : Category ℓo ℓh} {D : Category ℓo' ℓh'} (F : Functor C D) where
  open Map {ℓ = ℓ} {C = C} {D = D} F renaming (mapFunctor to Fam[F])

  open import Cubical.Categories.NaturalTransformation

  weakInverseMap : WeakInverse F → WeakInverse Fam[F]
  weakInverseMap winv = fam-winv where
    module G = Map {ℓ} (winv .WeakInverse.invFunc)

    fam-winv : WeakInverse Fam[F]
    fam-winv .WeakInverse.invFunc = G.mapFunctor
    fam-winv .WeakInverse.η .NatIso.trans .NatTrans.N-ob (J , c) = id ⟨ J ⟩ , {! !}
    fam-winv .WeakInverse.η .NatIso.trans .NatTrans.N-hom = {! !}
    fam-winv .WeakInverse.η .NatIso.nIso = {! !}
    fam-winv .WeakInverse.ε = {! !}

  isEquivalenceMap : isEquivalence F → isEquivalence Fam[F]
  isEquivalenceMap = PT.map weakInverseMap

module Elim {ℓ ℓo ℓh ℓo' ℓh'}
  {C : Category ℓo ℓh}
  {D : Category ℓo' ℓh'}
  (⨆D : Coproducts D ℓ)
  (F : Functor C D)
  where
  private
    module C = Category C
    Fam = Family.Fam ℓ C

    module Fam = Category Fam
    open Family.Notation ℓ C public

    module D where
      open Category D public
      open CoproductNotation D _ ⨆D public
    module F = Functor F renaming (F-ob to ₀ ; F-hom to ₁)

    elim₀ : Fam.ob → D.ob
    elim₀ (J , c) = D.⨆ J (F.₀ ∘ c)

    elim₁-equiv : (x y : Fam.ob) → D [ elim₀ x , elim₀ y ] ≃ (∀ j → D [ F.₀ (x .snd j) , elim₀ y ])
    elim₁-equiv x@(J , c) y = D.univ-equiv J (F.₀ ∘ c) (elim₀ y)

    module _ (x y : Fam.ob) where
      elim₁-univ : (∀ j → D [ F.₀ (x .snd j) , elim₀ y ]) → D [ elim₀ x , elim₀ y ]
      elim₁-univ = invEq (elim₁-equiv x y)

      elim₁-fam : Fam [ x , y ] → (∀ j → D [ F.₀ (El x j) , elim₀ y ])
      elim₁-fam (u , f) j = F.₁ (f j) D.⋆ D.ι (Index y) (F.₀ ∘ El y) (u j)

      elim₁ : Fam [ x , y ] → D [ elim₀ x , elim₀ y ]
      elim₁ = elim₁-fam ⋆ elim₁-univ

    opaque
      elim₁-id : (x : Fam.ob) → elim₁ x x Fam.id ≡ D.id {x = elim₀ x}
      elim₁-id x =
        elim₁-univ _ _ (elim₁-fam x x Fam.id) ≡⟨ cong (elim₁-univ x x) (funExt mangle) ⟩
        elim₁-univ _ _ (equivFun (elim₁-equiv x x) (D.id {x = elim₀ x})) ≡⟨ retEq (elim₁-equiv x x) _ ⟩
        D.id ∎ where

        mangle : (j : ⟨ Index x ⟩) → F.₁ C.id D.⋆ D.ι (Index x) (F.₀ ∘ El x) j ≡ D.ι _ _ _ D.⋆ D.id
        mangle j =
          F.₁ C.id D.⋆ D.ι _ _ _ ≡[ i ]⟨ F.F-id i D.⋆ D.ι _ _ _ ⟩
          D.id     D.⋆ D.ι _ _ _ ≡[ i ]⟨ D.⋆IdL (D.ι _ _ _) i ⟩
          D.ι _ _ _              ≡[ i ]⟨ D.⋆IdR (D.ι _ _ _) (~ i) ⟩
          D.ι _ _ _ D.⋆ D.id ∎

      elim₁-seq : (x y z : Fam.ob) (f : Fam [ x , y ]) (g : Fam [ y , z ])
        → elim₁ x z (f Fam.⋆ g) ≡ elim₁ x y f D.⋆ elim₁ y z g
      elim₁-seq = ?

  elimFunctor : Functor Fam D
  elimFunctor .Functor.F-ob = elim₀
  elimFunctor .Functor.F-hom {x} {y} = elim₁ x y
  elimFunctor .Functor.F-id {x} = elim₁-id x
  elimFunctor .Functor.F-seq {x} {y} {z} = elim₁-seq x y z
  {-# INJECTIVE_FOR_INFERENCE elimFunctor #-}
