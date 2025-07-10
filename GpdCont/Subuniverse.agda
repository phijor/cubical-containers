open import GpdCont.Prelude
open import GpdCont.Prelude.Square
open import GpdCont.Equiv using (equivPathEquiv ; symEquiv)
open import GpdCont.Univalence using (uaCompEquivSquare)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function using (3-Constant)
open import Cubical.Foundations.Transport using (substEquiv ; substComposite)
open import Cubical.Functions.FunExtEquiv
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

  hasOrd : (X : Type ℓ) → Type _
  hasOrd X = Σ[ a ∈ ⟨ U ⟩ ] ⟨ El a ⟩ ≃ X

  Ord : Type _
  Ord = TypeWithStr ℓ hasOrd

  ord : Ord → ⟨ U ⟩
  ord = fst ∘ snd

  hasOrd→isSub : ∀ {X} → hasOrd X → isSub X
  hasOrd→isSub (a , e) = PT.∣ a , e ∣₁

  Ord→Sub : Ord → hSetSub
  Ord→Sub = map-snd hasOrd→isSub

  -- hasOrd→merePath : ∀ {X} → (x y : hasOrd X) → x .fst ≡ y .fst → ∥ x ≡ y ∥₁
  -- hasOrd→merePath (a , e) (b , f) p = {! !}

  recWithEquiv : ∀ {ℓP} {P : Type ℓP}
    → (X : hSetSub)
    → isProp P
    → ((a : ⟨ U ⟩) → ⟨ El a ⟩ ≃ ⟨ X ⟩ → P)
    → P
  recWithEquiv {P} (X , is-sub-X) is-prop-P rec = ∃-rec is-prop-P rec is-sub-X

  isSubSub : (a : ⟨ U ⟩) → isSub ⟨ El a ⟩
  isSubSub a = ∃-intro a (idEquiv _)

  isSetTruncFunEl : isOfHLevelFun 2 El
  isSetTruncFunEl X = isSetΣ (str U) λ u → isOfHLevelPath' 2 isGroupoidHSet (El u) X

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

  uaEl : ∀ {a b : ⟨ U ⟩} → ⟨ El a ⟩ ≃ ⟨ El b ⟩ → inc a ≡ inc b
  uaEl = uaSub _ _

  uaSubId : (X : hSetSub) → uaSub X X (idEquiv ⟨ X ⟩) ≡ refl
  uaSubId X = ΣSquareProp (λ X → isPropIsSub) uaIdEquiv

  uaSubCompSquare : (X Y Z : hSetSub) → (e : ⟨ X ⟩ ≃ ⟨ Y ⟩) (f : ⟨ Y ⟩ ≃ ⟨ Z ⟩)
    → Square (uaSub X Y e) (uaSub X Z (e ∙ₑ f)) refl (uaSub Y Z f)
  uaSubCompSquare X Y Z e f = ΣSquareProp (λ X → isPropIsSub) (uaCompEquivSquare e f)

  uaSubComp : (X Y Z : hSetSub) → (e : ⟨ X ⟩ ≃ ⟨ Y ⟩) (f : ⟨ Y ⟩ ≃ ⟨ Z ⟩)
    → uaSub X Z (e ∙ₑ f) ≡ uaSub X Y e ∙ uaSub Y Z f
  uaSubComp X Y Z e f = sym (compSquareFillerUnique (uaSubCompSquare X Y Z e f))

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

  elimProp : ∀ {ℓP} {P : hSetSub → Type ℓP}
    → (∀ X → isProp (P X))
    → (∀ a → P (inc a))
    → ∀ X → P X
  elimProp {P} is-prop-P inc* = uncurry λ X → ∃-elim (λ is-sub-X → is-prop-P (X , is-sub-X)) $
    λ a (e : ⟨ El a ⟩ ≃ X) → subst P (uaSub (inc a) (X , _) e) $ inc* a

  elimPropᵉ : ∀ {ℓP} {P : hSetSub → Type ℓP}
    → (∀ X → isProp (P X))
    → (∀ X a → (e : ⟨ El a ⟩ ≃ X) → P (X , PT.∣ a , e ∣₁))
    → ∀ X → P X
  elimPropᵉ {P} is-prop-P inc* = uncurry λ X → ∃-elim (λ is-sub-X → is-prop-P (X , is-sub-X)) $ inc* X

  elimProp2 : ∀ {ℓP} {P : (X Y : hSetSub) → Type ℓP}
    → (∀ X Y → isProp (P X Y))
    → (∀ a b → P (inc a) (inc b))
    → ∀ X Y → P X Y
  elimProp2 {P} is-prop-P inc* = elimProp (λ X → isPropΠ λ Y → is-prop-P X Y) $ λ a → elimProp {P = P _} (is-prop-P _) (inc* a)

  rec : ∀ {ℓB} {B : Type ℓB}
    → (isGroupoid B)
    → (inc* : ⟨ U ⟩ → B)
    → (link* : ∀ {a b} → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩) → inc* a ≡ inc* b)
    → (comp* : ∀ {a b c}
        → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩)
        → (f : ⟨ El b ⟩ ≃ ⟨ El c ⟩)
        → Square
          (link* e)
          (link* (e ∙ₑ f))
          (refl′ (inc* a))
          (link* f)
      )
    → hSetSub → B
  rec {B} is-groupoid-B inc* link* comp* = uncurry goal where module _ (X : Type ℓ) where
    inc-X : hasOrd X → B
    inc-X (a , e) = inc* a

    link : (o₀ o₁ : hasOrd X) → inc-X o₀ ≡ inc-X o₁
    link (_ , e) (_ , f) = link* (e ∙ₑ invEquiv f)

    sq : (o₀ o₁ o₂ : hasOrd X) → Square (link o₀ o₁) (link o₀ o₂) refl (link o₁ o₂)
    sq (a , e) (b , f) (c , g) = goal where
      f⁻ = invEquiv f
      g⁻ = invEquiv g

      comp*-comp : Square (link* (e ∙ₑ f⁻)) (link* ((e ∙ₑ f⁻) ∙ₑ f ∙ₑ g⁻)) (refl′ (inc* a)) (link* (f ∙ₑ g⁻))
      comp*-comp = comp* (e ∙ₑ f⁻) (f ∙ₑ g⁻)

      smear : link* ((e ∙ₑ f⁻) ∙ₑ f ∙ₑ g⁻) ≡ link* (e ∙ₑ g⁻)
      smear = cong link* $ equivEq λ i → equivFun g⁻ ∘ (λ x → secEq f x i) ∘ equivFun e

      goal : Square (link* (e ∙ₑ f⁻)) (link* (e ∙ₑ g⁻)) refl (link* (f ∙ₑ g⁻))
      goal = λ i j → hcomp {φ = ∂ i ∨ ∂ j} (b* i j) (comp*-comp i j) where
        b* : (i j k : I) → Partial (∂ i ∨ ∂ j) B
        b* i j k (i = i0) = link* (e ∙ₑ f⁻) j
        b* i j k (i = i1) = smear k j
        b* i j k (j = i0) = inc* a
        b* i j k (j = i1) = link* (f ∙ₑ g⁻) i


    goal : (isSub X) → B
    goal = PT.rec→Gpd is-groupoid-B inc-X λ where
      .3-Constant.link → link
      .3-Constant.coh₁ → sq

  recSet : ∀ {ℓS} {S : Type ℓS}
    → (isSet S)
    → (inc* : ⟨ U ⟩ → S)
    → (link* : ∀ {a b} → ⟨ El a ⟩ ≃ ⟨ El b ⟩ → inc* a ≡ inc* b)
    → hSetSub → S
  recSet {S} is-set-S inc* link* = rec {B = S} (isSet→isGroupoid is-set-S) inc* link* comp* where
    comp* : ∀ {a b c}
      → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩)
      → (f : ⟨ El b ⟩ ≃ ⟨ El c ⟩)
      → Square
        (link* e)
        (link* (e ∙ₑ f))
        (refl′ (inc* a))
        (link* f)
    comp* e f = isSet→SquareP (λ _ _ → is-set-S) _ _ _ _

  pattern ∣_∣₁≡∣_∣₁ x y i =  PT.squash₁ PT.∣ x ∣₁ PT.∣ y ∣₁ i

  elim' : ∀ {ℓB} {B : hSetSub → Type ℓB}
    → (∀ X → isGroupoid (B X))
    → (inc* : ∀ X → (o : hasOrd X) → B (X , hasOrd→isSub o))
    → (link* : ∀ {X} → (o₀ o₁ : hasOrd X) → PathP (λ i → B (X , ∣ o₀ ∣₁≡∣ o₁ ∣₁ i)) (inc* X o₀) (inc* X o₁))
    → (comp* : ∀ {X} → (o₀ o₁ o₂ : hasOrd X)
        → SquareP (λ i j → B (X , PT.squash₁ PT.∣ o₀ ∣₁ (∣ o₁ ∣₁≡∣ o₂ ∣₁ i) j))
          (link* o₀ o₁)
          (link* o₀ o₂)
          refl
          (link* o₁ o₂)
      )
    → ∀ X → B X
  elim' {B} is-groupoid-B inc* link* comp* = uncurry goal where module _ (X : Type ℓ) where
    goal : (is-sub-X : isSub X) → B (X , is-sub-X)
    goal = PT.elim→Gpd _ (λ is-sub → is-groupoid-B (X , is-sub)) (inc* X) link* comp*

{-
  elim : ∀ {ℓB} {B : hSetSub → Type ℓB}
    → (∀ X → isGroupoid (B X))
    → (inc* : (a : ⟨ U ⟩) → B (inc a))
    → (path* : ∀ {a b} → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩) → PathP (λ i → B (uaEl e i)) (inc* a) (inc* b))
    → (comp* : ∀ {a b c}
        → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩)
        → (f : ⟨ El b ⟩ ≃ ⟨ El c ⟩)
        → SquareP (λ i j → B (uaSubCompSquare (inc a) (inc b) (inc c) e f i j))
          (path* e)
          (path* (e ∙ₑ f))
          (refl′ (inc* a))
          (path* f)
      )
    → ∀ X → B X
  elim {B} is-groupoid-B inc* path* comp* = uncurry goal where module _ (X : Type ℓ) where
    inc-X : (ord : hasOrd X) → B (X , hasOrd→isSub ord)
    inc-X (a , e) = subst B (uaSub (inc a) (X , _) e) (inc* a)

    path-X : (ord₀ ord₁ : hasOrd X) → PathP (λ i → B (X , PT.squash₁ (hasOrd→isSub ord₀) (hasOrd→isSub ord₁) i)) (inc-X ord₀) (inc-X ord₁)
    path-X (a , e) (b , f) i = comp B* {φ = ∂ i} ∂B B₀ where
      inc-path : inc a ≡ inc b
      inc-path = uaEl (e ∙ₑ invEquiv f)

      sub-square :
        Square {A = hSetSub}
          (uaSub (inc a) (X , _) e)
          (uaSub (inc b) (X , _) f)
          inc-path
          (λ i → X , PT.squash₁ PT.∣ a , e ∣₁ PT.∣ b , f ∣₁ i)
      sub-square = {!uaSubCompSquare (inc a) (X , ) (inc b) e (invEquiv f) !}

      B* : (j : I) → Type _
      B* j = B (sub-square i j)

      ∂B : (j : I) → Partial (∂ i) (B* j)
      ∂B j (i = i0) = {! !}
      ∂B j (i = i1) = {! !}

      B₀ : B* i0
      B₀ = path* (e ∙ₑ invEquiv f) i


    goal : (is-sub-X : isSub X) → B (X , is-sub-X)
    goal = PT.elim→Gpd _ (λ is-sub → is-groupoid-B (X , is-sub)) inc-X path-X {! !}

  elimSet : ∀ {ℓS} {S : hSetSub → Type ℓS}
    → (∀ X → isSet (S X))
    → (inc* : ∀ a → S (inc a))
    → (link* : ∀ {a b} → ⟨ El a ⟩ ≃ ⟨ El b ⟩ → inc* a ≡ inc* b)
    → ∀ X → S X
  elimSet {S} is-set-S inc* link* = ?
  -}

  elimSetOrd : ∀ {ℓS} {S : hSetSub → Type ℓS}
    → (∀ X → isSet (S X))
    → ((X : Type _) (a : ⟨ U ⟩) (e : ⟨ El a ⟩ ≃ X) → S (X , PT.∣ a , e ∣₁))
    → ∀ X → S X
  elimSetOrd {S} is-set-S rep = uncurry goal where module _ (X : Type ℓ) where
    on-ord : (x : Σ[ a ∈ ⟨ U ⟩ ] ⟨ El a ⟩ ≃ X) → S (X , PT.∣ x ∣₁)
    on-ord (a , e) = rep X a e

    well-defined : (x y : Σ[ a ∈ ⟨ U ⟩ ] ⟨ El a ⟩ ≃ X) → PathP (λ i → S (X , PT.squash₁ PT.∣ x ∣₁ PT.∣ y ∣₁ i)) (on-ord x) (on-ord y)
    well-defined (a , e) (b , f) i = {! !}

    goal : (is-sub-X : isSub X) → S (X , is-sub-X)
    goal = PT.elim→Set (λ is-sub-X → is-set-S (X , is-sub-X)) on-ord {! !}

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
      ≃⟨ ST.setTruncEquiv $ strictEquiv (λ (X , a , p) → (a , X , p)) (λ (a , X , p) → (X , a , p)) ⟩
    ∥ Σ[ a ∈ ⟨ U ⟩ ] Σ[ X ∈ Type ℓ ] ∥ ⟨ El a ⟩ ≃ X ∥₁ ∥₂
      ≃⟨ setTruncateSndΣ≃ ⟩
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

    hSetSub≃Card∞ : hSetSub ≃ Card∞
    hSetSub≃Card∞ = Σ-cong-equiv-snd isSub≃hasCode

    Card≃Code : Card ≃ ⟨ U ⟩
    Card≃Code =
      ∥ hSetSub ∥₂
        ≃⟨ setTruncEquiv hSetSub≃Card∞ ⟩
      ∥ Card∞ ∥₂
        ≃⟨ TruncCard∞≃Code ⟩
      ⟨ U ⟩
        ≃∎

    hasCodeOf : (X : hSetSub) → hasCode ⟨ X ⟩
    hasCodeOf (X , is-sub) = isSub→hasCode is-sub

    code : (X : hSetSub) → ⟨ U ⟩
    code X = hasCodeOf X .fst

    Representative : (X : hSetSub) → hSetSub
    Representative X = inc (code X)

    isRepresentative : (X : hSetSub) → ∥ Representative X ≡ X ∥₁
    isRepresentative X = PT.map (uaSub (Representative X) X) (hasCodeOf X .snd)

    isInjectiveElTrunc : (a b : ⟨ U ⟩) → ∥ ⟨ El a ⟩ ≃ ⟨ El b ⟩ ∥₁ → a ≡ b
    isInjectiveElTrunc a b e = cong fst $ is-strict ⟨ El b ⟩ (a , e) (b , PT.∣ idEquiv _ ∣₁)

    isInjectiveEl : (a b : ⟨ U ⟩) → ⟨ El a ⟩ ≃ ⟨ El b ⟩ → a ≡ b
    isInjectiveEl a b = isInjectiveElTrunc a b ∘ PT.∣_∣₁

    mereRep : (X Y : hSetSub) → ∥ (⟨ X ⟩ ≃ ⟨ Y ⟩ → ⟨ Representative X ⟩ ≃ ⟨ Representative Y ⟩) ∥₁
    mereRep = elimProp2 (λ X Y → PT.isPropPropTrunc) λ a b → PT.∣ id $ ⟨ El a ⟩ ≃ ⟨ El b ⟩ ∣₁

    hasSetFibersRepresentative' : (Y : hSetSub) → isSet (fiber Representative Y)
    -- hasSetFibersRepresentative' = elimPropᵉ (λ _ → isPropIsSet) λ Y a e → {! !}
    hasSetFibersRepresentative' = elimProp (λ _ → isPropIsSet) λ where
      a (X , e) (Y , f) → {!e !}

    hasSetFibersRepresentative : (Y : hSetSub) → isSet (fiber Representative Y)
    hasSetFibersRepresentative Y (X , e) (X' , e') = equivFun (PT.propTruncIdempotent≃ isPropIsProp) do
      rep-X ← isRepresentative X
      rep-X' ← isRepresentative X'
      return λ p p' → {! !}

    hasPropFibersRepresentative : (Y : hSetSub) → isProp (fiber Representative Y)
    hasPropFibersRepresentative Y (X , e) (X' , e') = PT.elim2→Set {P = λ r r' → (X , e) ≡ (X' , e')} {! !}
      (λ r r' → ΣPathP (sym r ∙∙ (e ∙ sym e') ∙∙ r' , {! !}))
      {! !}
      {! !}
      {! !}
      (isRepresentative X)
      (isRepresentative X')

    repMapSubst : (X Y : hSetSub) → ⟨ X ⟩ ≃ ⟨ Y ⟩ → ⟨ Representative X ⟩ ≃ ⟨ Representative Y ⟩
    repMapSubst X Y e = substEquiv (λ - → ⟨ Representative - ⟩) (uaSub X Y e)

    repMapJ : (X Y : hSetSub) → (p : X ≡ Y) → ⟨ Representative X ⟩ ≃ ⟨ Representative Y ⟩
    repMapJ X Y = J (λ Y p → ⟨ Representative X ⟩ ≃ ⟨ Representative Y ⟩) $ idEquiv ⟨ Representative X ⟩

    repMapJᵝ : (X : hSetSub) → repMapJ X X refl ≡ idEquiv ⟨ Representative X ⟩
    repMapJᵝ X = JRefl {x = X} (λ Y p → ⟨ Representative X ⟩ ≃ ⟨ Representative Y ⟩) (idEquiv ⟨ Representative X ⟩)

    repMapJEquiv : (X Y : hSetSub) → ⟨ X ⟩ ≃ ⟨ Y ⟩ → ⟨ Representative X ⟩ ≃ ⟨ Representative Y ⟩
    repMapJEquiv X Y = repMapJ X Y ∘ uaSub X Y

    repMapJEquiv-blah : (a : ⟨ U ⟩) → (e : ⟨ El a ⟩ ≃ ⟨ El a ⟩) → repMapJEquiv (inc a) (inc a) e ≡ e
    repMapJEquiv-blah a e =
      repMapJEquiv (inc a) (inc a) e ≡⟨ {! !} ⟩
      e ∎

    repMapJEquivᵝ : (X : hSetSub) → repMapJEquiv X X (idEquiv ⟨ X ⟩) ≡ idEquiv ⟨ Representative X ⟩
    repMapJEquivᵝ X =
      repMapJ X X (uaSub X X (idEquiv ⟨ X ⟩)) ≡⟨ {! !} ⟩
      repMapJ X X refl ≡⟨ {! !} ⟩
      idEquiv ⟨ Representative X ⟩ ∎

    conj : (X Y : Ord) → ⟨ X ⟩ ≃ ⟨ Y ⟩ → ⟨ El (ord X) ⟩ ≃ ⟨ El (ord Y) ⟩
    conj (X , a , El[a]≃X) (Y , b , El[b]≃Y) e = El[a]≃X ∙ₑ e ∙ₑ invEquiv El[b]≃Y

    -- conjᵁ : (a b : ⟨ U ⟩) → ⟨  ⟩ ≃ ⟨ Y ⟩ → ⟨ El (ord X) ⟩ ≃ ⟨ El (ord Y) ⟩
    -- conjᵁ (X , a , El[a]≃X) (Y , b , El[b]≃Y) e = El[a]≃X ∙ₑ e ∙ₑ invEquiv El[b]≃Y

    -- conj₁ : ∀ {X} → X ≃ X → (x : isSub X) → ⟨ Representative (X , x) ⟩ ≃ ⟨ Representative (X , x) ⟩
    -- conj₁ {X} σ = PT.elim→Set {! !} (λ { (a , e) → conj (X , a , e) (X , a , e) σ }) λ where
    --   (a , e) (b , f) → {! is-strict X (a , PT.∣ e ∣₁) !}

    repMapᵝ-path : ∀ {X Y} (e : X ≃ Y) → (x : hasOrd X) → (y : hasOrd Y)
      → repMapJEquiv (Ord→Sub (X , x)) (Ord→Sub (Y , y)) e ≡ conj (X , x) (Y , y) e
    repMapᵝ-path {Y} = EquivJ
      (λ X e → (x : hasOrd X) → (y : hasOrd Y) → repMapJEquiv (Ord→Sub (X , x)) (Ord→Sub (Y , y)) e ≡ conj (X , x) (Y , y) e)
      λ where
        (a , e) (b , f) →
          let Y₁ = (Y , a , e)
              Y₂ = (Y , b , f)
          in
          repMapJEquiv (Y , PT.∣ a , e ∣₁) (Y , PT.∣ b , f ∣₁) (idEquiv _) ≡⟨ {! !} ⟩
          -- repMapJEquiv (Ord→Sub Y₁) (Ord→Sub Y₁) ? ≡⟨ {! !} ⟩
          conj Y₁ Y₂ (idEquiv _) ∎

    repMapᵝ : ∀ (X Y : Ord) (e : ⟨ X ⟩ ≃ ⟨ Y ⟩) → repMapJEquiv (Ord→Sub X) (Ord→Sub Y) e ≡ conj X Y e
    repMapᵝ X Y e = equivEq {! !}

    repMapS : (X Y : hSetSub) → (e : ⟨ X ⟩ ≃ ⟨ Y ⟩) → singl (repMapJEquiv X Y e)
    -- repMapH = elimProp2 (λ X Y → isPropΠ λ e → isPropSingl) λ where
    --   a b e .fst → e
    --   a b e .snd → repMapᵝ a b e
    repMapS (X , is-sub-X) (Y , is-sub-Y) e = rep-map.helper e is-sub-X is-sub-Y where
      module rep-map {X Y : Type _} (e : X ≃ Y) where
        helper : (is-sub-X : isSub X) → (is-sub-Y : isSub Y) → singl $ repMapJEquiv (X , is-sub-X) (Y , is-sub-Y) e
        helper = PT.elim2 (λ _ _ → isPropSingl) λ where
          ord-x ord-y .fst → conj (X , ord-x) (Y , ord-y) e
          ord-x ord-y .snd → repMapᵝ (X , ord-x) (Y , ord-y) e

    repMap' : (X Y : hSetSub) → ⟨ X ⟩ ≃ ⟨ Y ⟩ → ⟨ Representative X ⟩ ≃ ⟨ Representative Y ⟩
    repMap' X Y e = repMapS X Y e .fst

    repΩ : {X : Type _} → X ≃ X → (e : isSub X) → ⟨ Representative (X , e) ⟩ ≃ ⟨ Representative (X , e) ⟩
    repΩ {X} k = PT.elim→Set {! !} (λ { (a , e) → e ∙ₑ k ∙ₑ invEquiv e }) λ where
        (a , e) (b , f) → let p = is-strict X (a , PT.∣ e ∣₁) (b , PT.∣ f ∣₁) in lemma a b (cong fst p) e f (cong snd p)
          -- toPathP $ equivEq $ funExt {! cong snd $ is-strict X (a , PT.∣ e ∣₁) (b , PT.∣ f ∣₁)  !}
      where
        lemma : (a b : ⟨ U ⟩) → (p : a ≡ b)
          → (e : ⟨ El a ⟩ ≃ X) (f : ⟨ El b ⟩ ≃ X)
          → (h : PathP (λ i → ∥ ⟨ El (p i) ⟩ ≃ X ∥₁) PT.∣ e ∣₁ PT.∣ f ∣₁)
          → PathP (λ i → ⟨ El (p i) ⟩ ≃ ⟨ El (p i) ⟩)
            (e ∙ₑ k ∙ₑ invEquiv e)
            (f ∙ₑ k ∙ₑ invEquiv f)
        lemma a b = J (λ b p
          → (e : ⟨ El a ⟩ ≃ X) (f : ⟨ El b ⟩ ≃ X)
          → (h : PathP (λ i → ∥ ⟨ El (p i) ⟩ ≃ X ∥₁) PT.∣ e ∣₁ PT.∣ f ∣₁)
          → PathP (λ i → ⟨ El (p i) ⟩ ≃ ⟨ El (p i) ⟩)
            (e ∙ₑ k ∙ₑ invEquiv e)
            (f ∙ₑ k ∙ₑ invEquiv f)
          )
          λ e f ∣p∣ → equivEq $ funExt {! !}

{-

    repMap' : (X Y : hSetSub) → ⟨ X ⟩ ≃ ⟨ Y ⟩ → ⟨ Representative X ⟩ ≃ ⟨ Representative Y ⟩
    repMap' (X , is-sub-X) (Y , is-sub-Y) e = rep-map.helper e is-sub-X is-sub-Y where module rep-map {X Y : Type _} (e : X ≃ Y) where
      -- conj : ((a , _) : Σ[ a ∈ ⟨ U ⟩ ] ⟨ El a ⟩ ≃ X) → ((b , _) : Σ[ a ∈ ⟨ U ⟩ ] ⟨ El a ⟩ ≃ Y) → ⟨ El a ⟩ ≃ ⟨ El b ⟩
      -- conj (a , El[a]≃X) (b , El[b]≃Y) = El[a]≃X ∙ₑ e ∙ₑ invEquiv El[b]≃Y

      helper' : (is-sub : ∥ (Σ[ a ∈ ⟨ U ⟩ ] ⟨ El a ⟩ ≃ X) × (Σ[ b ∈ ⟨ U ⟩ ] ⟨ El b ⟩ ≃ Y) ∥₁) → ⟨ Representative (X , PT.map fst is-sub) ⟩ ≃ ⟨ Representative (Y , PT.map snd is-sub) ⟩
      helper' = PT.elim→Set {! !} (λ (x , y) → conj x y) $ λ where
        ((a , El[a]≃X) , (b , El[b]≃Y)) ((a' , El[a']≃X) , (b' , El[b']≃Y)) → equivPathP {! !}

      helper : (is-sub-X : isSub X) → (is-sub-Y : isSub Y) → ⟨ Representative (X , is-sub-X) ⟩ ≃ ⟨ Representative (Y , is-sub-Y) ⟩
      helper = PT.elim2→Set
        (λ is-sub-X is-sub-Y → isOfHLevel≃ 2 (isSub→isSet $ str $ Representative (X , is-sub-X)) (isSub→isSet $ str $ Representative (Y , is-sub-Y)))
        conj
        (λ { (a , El[a]≃X) (a' , El[a']≃X) (b , El[b]≃Y) → equivPathP $
          let pp = is-strict X (a , PT.∣ El[a]≃X ∣₁) (a' , PT.∣ El[a']≃X ∣₁) in
          {! !}
          -- PT.rec (isOfHLevelPathP' 1 (isSet→ {!Y!}) _ _) {! !} {! cong snd pp  !}
          -- the (PathP (λ i → ⟨ El (pp i .fst) ⟩ → ⟨ El b ⟩) (invEq El[b]≃Y ∘ equivFun e ∘ equivFun El[a]≃X) (invEq El[b]≃Y ∘ equivFun e ∘ equivFun El[a']≃X))
          --   λ i → invEq El[b]≃Y ∘ equivFun e ∘ λ aᵢ → equivFun {!  pp i .snd !} aᵢ
          -- funExtNonDep λ {x₀} {x₁} p →
          -- invEq El[b]≃Y (equivFun e (equivFun El[a]≃X x₀)) ≡[ i ]⟨ invEq El[b]≃Y (equivFun e {! is-strict _ (a , PT.∣ El[a]≃X ∣₁) (a' , PT.∣ El[a']≃X ∣₁) i !}) ⟩
          -- invEq El[b]≃Y (equivFun e (equivFun El[a']≃X x₁)) ∎
        })
        {! !}
        (λ x y v w →
          isSet→SquareP {A = λ i j → ⟨ Representative (X , PT.squash₁ PT.∣ x ∣₁ PT.∣ y ∣₁ i) ⟩ ≃ ⟨ Representative (Y , PT.squash₁ PT.∣ v ∣₁ PT.∣ w ∣₁ j) ⟩}
            (λ i j → isOfHLevel≃ 2 {! !} {! !})
            _ _ _ _
        )
        -}


    isConterFibersRepMap : (X Y : hSetSub) → (k : ⟨ Representative X ⟩ ≃ ⟨ Representative Y ⟩) → isContr (fiber (repMap' X Y) k)
    isConterFibersRepMap = elimProp2 (λ X Y → isPropΠ λ k → isPropIsContr) is-contr-fib where
      module _ (a b : ⟨ U ⟩) (k : ⟨ El a ⟩ ≃ ⟨ El b ⟩) where
        a≡b : a ≡ b
        a≡b = cong fst (is-strict ⟨ El b ⟩ (a , PT.∣ k ∣₁) (b , PT.∣ idEquiv _ ∣₁))

        fiber-equiv : singl k ≃ fiber (repMap' (inc a) (inc b)) k
        fiber-equiv =
          singl k ≃⟨ Σ-cong-equiv-snd (λ α → symEquiv) ⟩
          Σ[ α ∈ ⟨ El a ⟩ ≃ ⟨ El b ⟩ ] α ≡ k ≃⟨ Σ-cong-equiv-snd (λ α → compPathlEquiv $ equivEq refl) ⟩
          Σ[ α ∈ ⟨ El a ⟩ ≃ ⟨ El b ⟩ ] idEquiv ⟨ El a ⟩ ∙ₑ α ∙ₑ (invEquiv $ idEquiv _) ≡ k ≃⟨⟩
          fiber (repMap' (inc a) (inc b)) k ≃∎

        is-contr-fib : isContr (fiber (repMap' (inc a) (inc b)) k)
        is-contr-fib = isOfHLevelRespectEquiv 0 fiber-equiv (isContrSingl k)

    isEquivRepMap : (X Y : hSetSub) → isEquiv (repMap' X Y)
    isEquivRepMap X Y .equiv-proof = isConterFibersRepMap X Y

    repMapSubstComp : (X Y Z : hSetSub) → (e : ⟨ X ⟩ ≃ ⟨ Y ⟩) → (f : ⟨ Y ⟩ ≃ ⟨ Z ⟩)
      → repMapSubst X Z (e ∙ₑ f) ≡ repMapSubst X Y e ∙ₑ repMapSubst Y Z f
    repMapSubstComp X Y Z e f = equivEq $
      subst (λ - → ⟨ Representative - ⟩) (uaSub X Z (e ∙ₑ f)) ≡⟨ cong (subst (λ - → ⟨ Representative - ⟩)) $ uaSubComp X Y Z e f ⟩
      subst (λ - → ⟨ Representative - ⟩) (uaSub X Y e ∙ uaSub Y Z f) ≡⟨ funExt $ substComposite (⟨_⟩ ∘ Representative) (uaSub X Y e) (uaSub Y Z f) ⟩
      subst (λ - → ⟨ Representative - ⟩) (uaSub X Y e) ⋆ subst (λ - → ⟨ Representative - ⟩) (uaSub Y Z f) ∎

    repMapComp : (X Y Z : hSetSub) → (e : ⟨ X ⟩ ≃ ⟨ Y ⟩) → (f : ⟨ Y ⟩ ≃ ⟨ Z ⟩)
      → repMap' X Z (e ∙ₑ f) ≡ repMap' X Y e ∙ₑ repMap' Y Z f
    repMapComp X Y Z e f = {! !}

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
      pairᵁ : (A : ⟨ U ⟩) (B : ⟨ El A ⟩ → ⟨ U ⟩) → ⟨ El (Σᵁ A B) ⟩ ≃ (Σ[ a ∈ ⟨ El A ⟩ ] ⟨ El (B a) ⟩)
      choice : ∀ {A : Type ℓ} {B : A → Type ℓ} → isSub A → (∀ a → isSub (B a)) → ∥ (∀ a → Σ[ b ∈ ⟨ U ⟩ ] ⟨ El b ⟩ ≃ B a) ∥₁

    isSubΣ : ∀ {A : Type ℓ} {B : A → Type ℓ}
      → isSub A
      → (∀ a → isSub (B a))
      → isSub (Σ A B)
    isSubΣ {A} {B} is-sub-A is-sub-B = do
      aᵁ , e ← is-sub-A
      sub ← choice is-sub-A is-sub-B
      let bᵁ = fst ∘ sub
          eᴰ = snd ∘ sub
      return λ where
        .fst → Σᵁ aᵁ (bᵁ ∘ equivFun e)
        .snd →
          ⟨ El (Σᵁ aᵁ (bᵁ ∘ equivFun e)) ⟩
            ≃⟨ pairᵁ aᵁ (bᵁ ∘ equivFun e) ⟩
          Σ[ a ∈ ⟨ El aᵁ ⟩ ] ⟨ El (bᵁ (equivFun e a))⟩
            ≃⟨ Σ-cong-equiv e $ (eᴰ ∘ equivFun e) ⟩
          Σ A B
            ≃∎


    SubΣ : (A : hSetSub) (B : ⟨ A ⟩ → hSetSub) → hSetSub
    SubΣ A B .fst = Σ ⟨ A ⟩ (⟨_⟩ ∘ B)
    SubΣ A B .snd = isSubΣ (str A) (str ∘ B)
