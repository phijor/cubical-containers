open import GpdCont.Prelude
open import GpdCont.Prelude.Square

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)

open import GpdCont.SetTruncation as ST
open import GpdCont.Connectivity

module GpdCont.Subuniverse {ℓ} (U : hSet ℓ) (El : ⟨ U ⟩ → hSet ℓ) where
  isSub : (X : Type ℓ) → Type _
  isSub X = ∃[ a ∈ ⟨ U ⟩ ] ⟨ El a ⟩ ≃ X

  isPropIsSub : {X : Type ℓ} → isProp (isSub X)
  isPropIsSub {X} = isProp∃ _ _
  
  hSetSub : Type _
  hSetSub = TypeWithStr ℓ isSub

  isSubSub : (a : ⟨ U ⟩) → isSub ⟨ El a ⟩
  isSubSub a = ∃-intro a (idEquiv _)

  inc : ⟨ U ⟩ → hSetSub
  inc a .fst = ⟨ El a ⟩
  inc a .snd = isSubSub a

  isSub→isSet : ∀ {X} → isSub X → isSet X
  isSub→isSet {X} = ∃-rec isPropIsSet λ a El[a]≃X → isOfHLevelRespectEquiv 2 El[a]≃X (str (El a))

  ⟨_⟩ˢ : hSetSub → hSet ℓ
  ⟨ X , is-sub ⟩ˢ .fst = X
  ⟨ X , is-sub ⟩ˢ .snd = isSub→isSet is-sub

  SubPath≃ : (X Y : hSetSub) → (⟨ X ⟩ ≡ ⟨ Y ⟩) ≃ (X ≡ Y)
  SubPath≃ _ _ = Σ≡PropEquiv λ X → isPropIsSub

  uaSub : (X Y : hSetSub) → ⟨ X ⟩ ≃ ⟨ Y ⟩ → X ≡ Y
  uaSub X Y e = equivFun (SubPath≃ X Y) $ ua e

  isGroupoidHSetSub : isGroupoid hSetSub
  isGroupoidHSetSub X Y = isOfHLevelRespectEquiv 2 (SubPath≃ X Y) (isOfHLevel≡ 2 (isSub→isSet (str X)) (isSub→isSet (str Y)))

  Card : Type _
  Card = ∥ hSetSub ∥₂

  isSetCard : isSet Card
  isSetCard = ST.isSetSetTrunc
  
  hasCode : (X : Type ℓ) → Type ℓ
  hasCode X = Σ[ a ∈ ⟨ U ⟩ ] ∥ ⟨ El a ⟩ ≃ X ∥₁

  isStrict : Type _
  isStrict = ∀ X → isProp (hasCode X)

  Card∞ : Type _
  Card∞ = TypeWithStr ℓ hasCode

  hasCode→isSub : ∀ {X} → hasCode X → isSub X
  hasCode→isSub = uncurry λ a → PT.map (a ,_)

  elimSet : ∀ {ℓS} (S : hSetSub → hSet ℓS)
    → (∀ a → ⟨ S (inc a) ⟩)
    → ∀ X → ⟨ S X ⟩
  elimSet S rep = uncurry goal where module _ (X : Type ℓ) where
    on-ord : (e : hasCode X) → ⟨ S (X , PT.∣ {! !} ∣₁) ⟩
    on-ord (a , e) = {!rep a !}

    goal : (is-sub-X : isSub X) → ⟨ S (X , is-sub-X) ⟩
    goal = PT.elim→Set (λ is-sub-X → str (S (X , is-sub-X))) {! !} {! !}


  isConnectedElComponent : (a : ⟨ U ⟩) → isPathConnected (Σ[ X ∈ Type ℓ ] ∥ ⟨ El a ⟩ ≃ X ∥₁)
  isConnectedElComponent a = pointed×merePath→isPathConnected (⟨ El a ⟩ , PT.∣ idEquiv _ ∣₁) $
    uncurry
    λ X → PT.elim (λ _ → isPropΠ λ _ → PT.isPropPropTrunc)
    λ e → uncurry
    λ Y → PT.elim (λ _ → PT.isPropPropTrunc)
    λ f → PT.∣ Σ≡Prop (λ _ → PT.isPropPropTrunc) (ua (invEquiv e ∙ₑ f)) ∣₁

  TruncCard∞≃Code : ∥ Card∞ ∥₂ ≃ ⟨ U ⟩
  TruncCard∞≃Code =
    ∥ Σ[ X ∈ Type _ ] hasCode X ∥₂
      ≃⟨⟩
    ∥ Σ[ X ∈ Type _ ] Σ[ a ∈ ⟨ U ⟩ ] ∥ ⟨ El a ⟩ ≃ X ∥₁ ∥₂
      ≃⟨ {! !} ⟩
    ∥ Σ[ a ∈ ⟨ U ⟩ ] Σ[ X ∈ Type ℓ ] ∥ ⟨ El a ⟩ ≃ X ∥₁ ∥₂
      ≃⟨ {! !} ⟩
    ∥ Σ[ a ∈ ⟨ U ⟩ ] ∥ Σ[ X ∈ Type ℓ ] ∥ ⟨ El a ⟩ ≃ X ∥₁ ∥₂ ∥₂
      ≃⟨ ST.setTruncEquiv (Σ-contractSnd isConnectedElComponent) ⟩
    ∥ ⟨ U ⟩ ∥₂
      ≃⟨ ST.setTruncIdempotent≃ (str U) ⟩
    ⟨ U ⟩
      ≃∎

  module Strict (is-strict : isStrict) where
    isSub→hasCode : ∀ {X} → isSub X → hasCode X
    isSub→hasCode = ∃-rec (is-strict _) λ a e → a , PT.∣ e ∣₁

    isSub≃hasCode : ∀ X → isSub X ≃ hasCode X
    isSub≃hasCode X = propBiimpl→Equiv isPropIsSub (is-strict X) isSub→hasCode hasCode→isSub

    Card≃Code : Card ≃ ⟨ U ⟩
    Card≃Code =
      ∥ Σ[ X ∈ Type _ ] isSub X ∥₂
        ≃⟨ setTruncEquiv (Σ-cong-equiv-snd isSub≃hasCode) ⟩
      ∥ Σ[ X ∈ Type _ ] hasCode X ∥₂
        ≃⟨ TruncCard∞≃Code ⟩
      ⟨ U ⟩
        ≃∎

    hasCodeOf : (X : hSetSub) → hasCode ⟨ X ⟩
    hasCodeOf (X , is-sub) = isSub→hasCode is-sub

    Representative : (X : hSetSub) → hSetSub
    Representative X = inc (fst (hasCodeOf X))

    isRepresentative : (X : hSetSub) → ∥ Representative X ≡ X ∥₁
    isRepresentative X = PT.map (uaSub (Representative X) X) (hasCodeOf X .snd)

    module isStrict→TruncSplitSection where
      is-groupoid-fiber : (κ : Card) → isGroupoid (fiber ∣_∣₂ κ)
      is-groupoid-fiber = isOfHLevelFiber 3 isGroupoidHSetSub (isOfHLevelPlus {n = 2} 2 isSetCard) ∣_∣₂

      [-]* : (X : hSetSub) → fiber ∣_∣₂ ∣ X ∣₂
      [-]* X .fst = Representative X
      [-]* X .snd = merePath→pathSetTrunc (isRepresentative X)

      module _ (X Y : hSetSub) (p q : X ≡ Y) where
        card-square : SquareP (λ i j → ⟨ U ⟩)
          (cong (fst ∘ hasCodeOf) p)
          (cong (fst ∘ hasCodeOf) q)
          refl
          refl
        card-square = isSet→SquareP (λ i j → str U) _ _ _ _

        rep-square : SquareP (λ i j → ∣ inc (card-square i j) ∣₂ ≡ (ST.squash-cong p q i j))
          (λ i → merePath→pathSetTrunc (isRepresentative (p i)))
          (λ i → merePath→pathSetTrunc (isRepresentative (q i)))
          refl
          refl
        rep-square = isProp→SquareP (λ i j → ST.isSetSetTrunc ∣ inc (card-square i j) ∣₂ (ST.squash-cong p q i j)) _ _ _ _

        well-defined : SquareP (λ i j → fiber ∣_∣₂ (ST.squash-cong p q i j)) (cong [-]* p) (cong [-]* q) refl refl
        well-defined i j .fst = inc (card-square i j)
        well-defined i j .snd = rep-square i j

      open ST.elim→Gpd is-groupoid-fiber [-]* well-defined public

    open isStrict→TruncSplitSection using ()
      renaming
        ( fun to isStrict→TruncSplitSection
        ; funᵝ to isStrict→TruncSplitSectionᵝ
        )
        
    pt : Card → hSetSub
    pt = fst ∘ isStrict→TruncSplitSection

    ptᵝ : (X : hSetSub) → pt ∣ X ∣₂ ≡ Representative X
    ptᵝ X = cong fst (isStrict→TruncSplitSectionᵝ X)

  record hasSigma : Type (ℓ-suc ℓ) where
    no-eta-equality
    field
      Σᵁ : (a : ⟨ U ⟩) → (b : ⟨ El a ⟩ → ⟨ U ⟩) → ⟨ U ⟩
      choice : ∀ {A : Type ℓ} {B : A → Type ℓ} → isSub A → (∀ a → isSub (B a)) → ∥ (∀ a → Σ[ b ∈ ⟨ U ⟩ ] ⟨ El b ⟩ ≃ B a) ∥₁

    isSubΣ : ∀ {A : Type ℓ} {B : A → Type ℓ}
      → isSub A
      → (∀ a → isSub (B a))
      → isSub (Σ A B)
    isSubΣ {A} {B} is-sub-A is-sub-B = do
      aᵁ , e ← is-sub-A
      sub ← choice is-sub-A is-sub-B
      let bᵁ = fst ∘ sub
          eᵁ = snd ∘ sub
      return λ where
        .fst → Σᵁ aᵁ (bᵁ ∘ equivFun e)
        .snd →
          ⟨ El (Σᵁ aᵁ (bᵁ ∘ equivFun e)) ⟩
            ≃⟨ {! !} ⟩
          Σ A (⟨_⟩ ∘ El ∘ bᵁ)
            ≃⟨ Σ-cong-equiv-snd eᵁ ⟩
          Σ A B
            ≃∎


    SubΣ : (A : hSetSub) (B : ⟨ A ⟩ → hSetSub) → hSetSub
    SubΣ A B .fst = Σ ⟨ A ⟩ (⟨_⟩ ∘ B)
    SubΣ A B .snd = isSubΣ (str A) (str ∘ B)
