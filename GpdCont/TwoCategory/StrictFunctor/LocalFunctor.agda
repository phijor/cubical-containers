open import GpdCont.Prelude
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.StrictFunctor
open import GpdCont.TwoCategory.LocalCategory

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence ; WeakEquivalence)

module GpdCont.TwoCategory.StrictFunctor.LocalFunctor
  {ℓo ℓo′ ℓh ℓh′ ℓr ℓr′}
  {C : TwoCategory ℓo ℓh ℓr}
  {D : TwoCategory ℓo′ ℓh′ ℓr′}
  (F : StrictFunctor C D)
  where
    private
      module C = TwoCategory C
      module D = TwoCategory D
      module F = StrictFunctor F

      C[_,_] = LocalCategory C
      D[_,_] = LocalCategory D

    LocalFunctor : (x y : C.ob) → Functor C[ x , y ] D[ F.₀ x , F.₀ y ]
    LocalFunctor x y .Functor.F-ob = F.₁
    LocalFunctor x y .Functor.F-hom = F.₂
    LocalFunctor x y .Functor.F-id = F.F-rel-id
    LocalFunctor x y .Functor.F-seq = F.F-rel-trans

    Locally : ∀ {ℓ} (P : ∀ {C : Category ℓh ℓr} {D : Category ℓh′ ℓr′} → Functor C D → Type ℓ) → Type _
    Locally P = ∀ (x y : C.ob) → P (LocalFunctor x y)

    isLocallyFullyFaithful : Type _
    isLocallyFullyFaithful = Locally Functor.isFullyFaithful

    isLocallyEssentiallySurjective : Type _
    isLocallyEssentiallySurjective = Locally Functor.isEssentiallySurj

    isLocallySplitEssentiallySurjective : Type _
    isLocallySplitEssentiallySurjective = Locally isSplitEssentiallySurjective where
      isSplitEssentiallySurjective : ∀ {C : Category ℓh ℓr} {D : Category ℓh′ ℓr′} → Functor C D → Type _
      isSplitEssentiallySurjective {C} {D} F = (d : D .ob) → Σ[ c ∈ C .ob ] CatIso D (F .F-ob c) d where
        open Category
        open Functor

    localEmbedding : isLocallyFullyFaithful
      → ∀ {x y : C.ob} (f g : C.hom x y)
      → C.rel f g ≃ D.rel (F.₁ f) (F.₁ g)
    localEmbedding is-ff f g .fst = F.₂
    localEmbedding is-ff f g .snd = is-ff _ _ f g

    isLocallyWeakEquivalence : Type _
    isLocallyWeakEquivalence = Locally isWeakEquivalence

    isLocallyFullyFaithful×EssentiallySurjective→isLocallyWeakEquivalence :
      isLocallyFullyFaithful → isLocallyEssentiallySurjective → isLocallyWeakEquivalence
    isLocallyFullyFaithful×EssentiallySurjective→isLocallyWeakEquivalence ff eso x y .isWeakEquivalence.fullfaith = ff x y
    isLocallyFullyFaithful×EssentiallySurjective→isLocallyWeakEquivalence ff eso x y .isWeakEquivalence.esssurj = eso x y

    localWeakEquivalence : isLocallyWeakEquivalence → ∀ (x y : C.ob) → WeakEquivalence (LocalCategory C x y) (LocalCategory D (F.₀ x) (F.₀ y))
    localWeakEquivalence is-weq x y .WeakEquivalence.func = LocalFunctor x y
    localWeakEquivalence is-weq x y .WeakEquivalence.isWeakEquiv = is-weq x y
