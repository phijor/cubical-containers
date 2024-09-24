{-# OPTIONS --lossy-unification #-}

open import GpdCont.Prelude
open import Cubical.Algebra.Group.Base as AbsGroup renaming (GroupStr to AbsGroupStr ; Group to AbsGroup)
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)
open import Cubical.Algebra.Group.GroupPath using (uaGroup)
open import Cubical.Algebra.SymmetricGroup using (Symmetric-Group)

module GpdCont.Delooping.Properties {ℓ} (G : Type ℓ) (γ : AbsGroupStr G) where
private
  open module G = AbsGroupStr γ using (_·_ ; inv)

open import GpdCont.Groups.Base
open import GpdCont.Delooping.Base G γ as Delooping using (𝔹)
open import GpdCont.Connectivity using (isPathConnected)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using (compPath→Square)
open import Cubical.Foundations.Univalence hiding (elimIso)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.Functions.Embedding

isPropSetTruncDelooping : isProp ∥ 𝔹 ∥₂
isPropSetTruncDelooping = ST.elim2 (λ s t → ST.isSetPathImplicit) conn-lemma where
  conn-lemma : (s t : 𝔹) → ST.∣ s ∣₂ ≡ ST.∣ t ∣₂
  conn-lemma = Delooping.elimProp {B = λ s → (t : 𝔹) → ST.∣ s ∣₂ ≡ ST.∣ t ∣₂}
    (λ s → isPropΠ λ t → ST.isSetSetTrunc _ _)
    (Delooping.elimProp (λ t → ST.isSetSetTrunc _ _) $ refl {x = ST.∣ Delooping.⋆ ∣₂})

isConnectedDelooping : isContr ∥ 𝔹 ∥₂
isConnectedDelooping = inhProp→isContr ST.∣ 𝔹.⋆ ∣₂ isPropSetTruncDelooping

deloopingGroupStr : GroupStr 𝔹
deloopingGroupStr .GroupStr.is-connected = isConnectedDelooping
deloopingGroupStr .GroupStr.is-groupoid = Delooping.isGroupoid𝔹
deloopingGroupStr .GroupStr.pt = Delooping.⋆

coerceLoopCompSquareFiller : ∀ {g h r}
  → g · h ≡ r
  → compSquareFiller (𝔹.loop g) (𝔹.loop h) (𝔹.loop r)
coerceLoopCompSquareFiller {g} {h} {r} p i j = hcomp {φ = i ∨ ~ i ∨ j ∨ ~ j}
  (λ where
    k (i = i0) → Delooping.loop g j
    k (i = i1) → Delooping.loop (p k) j
    k (j = i0) → Delooping.⋆
    k (j = i1) → Delooping.loop h i
  )
  (𝔹.loop-comp g h i j)

private
  conjugate : (g : G) → G → G
  conjugate g h = inv g · h · g

  conjugateIso : (g : G) → Iso G G
  conjugateIso g .Iso.fun = conjugate g
  conjugateIso g .Iso.inv = conjugate (inv g)
  conjugateIso g .Iso.rightInv h =
    inv g · (inv (inv g) · h · inv g) · g ≡⟨ {! !} ⟩
    h ∎
  conjugateIso g .Iso.leftInv h =
    inv (inv g) · (inv g · h · g) · inv g ≡⟨ {! !} ⟩
    h ∎

  conjugateEquiv : (g : G) → G ≃ G
  conjugateEquiv g = isoToEquiv $ conjugateIso g

  conjugatePath : (g : G) → G ≡ G
  conjugatePath g = ua $ conjugateEquiv g

  conjugatePathFiller : ∀ g h → compSquareFiller (conjugatePath g) (conjugatePath h) (conjugatePath $ g · h)
  conjugatePathFiller g h = coerceCompSquareFiller $
    ua (conjugateEquiv g) ∙ ua (conjugateEquiv h) ≡⟨ sym (uaCompEquiv _ _) ⟩
    ua (conjugateEquiv g ∙ₑ conjugateEquiv h) ≡⟨ cong ua $ equivEq $ funExt shuffle ⟩
    ua (conjugateEquiv $ g · h) ∎
    where
      shuffle : ∀ x → inv h · (inv g · x · g) · h ≡ inv (g · h) · x · g · h
      shuffle = {! !}

  mulRightIso : (g : G) → Iso G G
  mulRightIso g .Iso.fun = _· g
  mulRightIso g .Iso.inv = _· (inv g)
  mulRightIso g .Iso.rightInv = {! !}
  mulRightIso g .Iso.leftInv = {! !}

  mulRightEquiv : (g : G) → G ≃ G
  mulRightEquiv g = isoToEquiv $ mulRightIso g

  mulRightPath : (g : G) → G ≡ G
  mulRightPath g = ua $ mulRightEquiv g

  opaque
    mulRightPathFiller : ∀ g h → compSquareFiller (mulRightPath g) (mulRightPath h) (mulRightPath $ g · h)
    mulRightPathFiller g h = coerceCompSquareFiller $
      ua (mulRightEquiv g) ∙ ua (mulRightEquiv h) ≡⟨ sym (uaCompEquiv _ _) ⟩
      ua (mulRightEquiv g ∙ₑ mulRightEquiv h) ≡⟨ cong ua $ equivEq $ funExt (λ k → sym (G.·Assoc k g h)) ⟩
      ua (mulRightEquiv $ g · h) ∎

Code : 𝔹 → hSet ℓ
Code = Delooping.rec isGroupoidHSet Code[⋆≡⋆] Code[⋆≡_] filler where
  Code[⋆≡⋆] : hSet ℓ
  Code[⋆≡⋆] .fst = G
  Code[⋆≡⋆] .snd = AbsGroupStr.is-set γ

  Code[⋆≡_] : G → Code[⋆≡⋆] ≡ Code[⋆≡⋆]
  Code[⋆≡_] g = TypeOfHLevel≡ 2 (mulRightPath g)

  filler : ∀ g h → compSquareFiller Code[⋆≡ g ] Code[⋆≡ h ] Code[⋆≡ g · h ]
  filler g h = ΣSquareSet (λ _ → isProp→isSet isPropIsSet) (mulRightPathFiller g h)

isSetCode : ∀ x → isSet ⟨ Code x ⟩
isSetCode = str ∘ Code

encode : ∀ {y} → 𝔹.⋆ ≡ y → ⟨ Code y ⟩
encode = J (λ y p → ⟨ Code y ⟩) G.1g

encodeRefl : encode refl ≡ G.1g
encodeRefl = JRefl (λ y p → ⟨ Code y ⟩) G.1g

decode : ∀ {y} → ⟨ Code y ⟩ → 𝔹.⋆ ≡ y
decode {y} = decode' y where
  decode' : ∀ y → ⟨ Code y ⟩ → 𝔹.⋆ ≡ y
  decode' = Delooping.elimSet (λ x → isSet→ (𝔹.isGroupoid𝔹 𝔹.⋆ x))
    𝔹.loop
    λ { g → ua→ λ h → 𝔹.loop-comp h g }

decode-encode : ∀ {y} (p : 𝔹.⋆ ≡ y) → decode (encode p) ≡ p
decode-encode = J (λ y p → decode (encode p) ≡ p) $
  decode (encode refl) ≡⟨ cong decode encodeRefl ⟩
  decode G.1g ≡⟨ Delooping.loop-1 ⟩
  refl ∎

encode-decode : ∀ y (c : ⟨ Code y ⟩) → encode (decode c) ≡ c
encode-decode = Delooping.elimProp (λ _ → isPropΠ λ c → isSetCode _ _ _) λ g →
  transport refl (G.1g · g) ≡⟨ transportRefl _ ⟩
  G.1g · g ≡⟨ G.·IdL g ⟩
  g ∎

encodeDecodeIso : ∀ {y} → Iso (𝔹.⋆ ≡ y) ⟨ Code y ⟩
encodeDecodeIso .Iso.fun = encode
encodeDecodeIso .Iso.inv = decode
encodeDecodeIso .Iso.rightInv = encode-decode _
encodeDecodeIso .Iso.leftInv = decode-encode

encodeDecode : ∀ {y} → (𝔹.⋆ ≡ y) ≃ ⟨ Code y ⟩
encodeDecode = isoToEquiv encodeDecodeIso

ΩDelooping≃ : (𝔹.⋆ ≡ 𝔹.⋆) ≃ G
ΩDelooping≃ = encodeDecode {y = 𝔹.⋆}

π₁ : ∀ {ℓX} (X : hGroupoid ℓX) (x₀ : ⟨ X ⟩) → AbsGroup _
π₁ X x₀ .fst = x₀ ≡ x₀
π₁ X x₀ .snd .AbsGroupStr.1g = refl
π₁ X x₀ .snd .AbsGroupStr._·_ = _∙_
π₁ X x₀ .snd .AbsGroupStr.inv = sym
π₁ X x₀ .snd .AbsGroupStr.isGroup = makeIsGroup (str X x₀ x₀) assoc (sym ∘ rUnit) (sym ∘ lUnit) rCancel lCancel where
  open import Cubical.Foundations.GroupoidLaws

elimSetIso : ∀ {ℓB} {B : 𝔹 → Type ℓB}
  → (∀ x → isSet (B x))
  → Iso (Σ[ b₀ ∈ B 𝔹.⋆ ] (∀ g → PathP (λ i → B (𝔹.loop g i)) b₀ b₀)) (∀ x → B x)
elimSetIso is-set-B .Iso.fun = uncurry $ Delooping.elimSet is-set-B
elimSetIso is-set-B .Iso.inv b = b 𝔹.⋆ , cong b ∘ 𝔹.loop
elimSetIso is-set-B .Iso.rightInv b = funExt (Delooping.elimProp (λ _ → isOfHLevelPathP' 1 (is-set-B _) _ _) refl)
elimSetIso is-set-B .Iso.leftInv (b₀ , p) = refl

elimSetEquiv : ∀ {ℓB} {B : 𝔹 → Type ℓB}
  → (∀ x → isSet (B x))
  → (Σ[ b₀ ∈ B 𝔹.⋆ ] (∀ g → PathP (λ i → B (𝔹.loop g i)) b₀ b₀)) ≃ (∀ x → B x)
elimSetEquiv = isoToEquiv ∘ elimSetIso

recEquiv : ∀ {ℓX} {X : hGroupoid ℓX}
  → (Σ[ x₀ ∈ ⟨ X ⟩ ] Σ[ φ ∈ (G → x₀ ≡ x₀) ] ∀ g h → compSquareFiller (φ g) (φ h) (φ $ g · h)) ≃ (𝔹 → ⟨ X ⟩)
recEquiv {X = (X , is-gpd-X)} = rec-equiv , is-equiv where
  open IsGroupHom using (pres·)
  open import Cubical.Data.Sigma
  rec-equiv : _ → _
  rec-equiv (x₀ , φ , φ-hom) = Delooping.rec is-gpd-X x₀ φ φ-hom

  rec-inv : (𝔹 → X) → (Σ[ x₀ ∈ X ] Σ[ φ ∈ (G → x₀ ≡ x₀) ] ∀ g h → compSquareFiller (φ g) (φ h) (φ $ g · h))
  rec-inv f .fst = f 𝔹.⋆
  rec-inv f .snd .fst = cong f ∘ 𝔹.loop
  rec-inv f .snd .snd = λ g h i j → f (Delooping.loop-comp g h i j)

  recIso : Iso _ _
  recIso .Iso.fun = rec-equiv
  recIso .Iso.inv = rec-inv
  recIso .Iso.rightInv f = funExt (Delooping.elim (λ _ → isSet→isGroupoid (is-gpd-X _ _)) refl (λ g i j → f (𝔹.loop g i)) λ g h i j k → f (𝔹.loop-comp g h i j))
  recIso .Iso.leftInv (x₀ , φ , φ-comp) = refl

  is-equiv : isEquiv rec-equiv
  is-equiv = isoToIsEquiv recIso

private
  variable
    ℓ' : Level
    A B C : Type ℓ'

  isTruncatedFun : (k : HLevel) (f : A → B) → Type _
  isTruncatedFun k f = ∀ b → isOfHLevel k (fiber f b)

  isTruncatedFunComp : (k : HLevel) {f : A → B} {g : B → C} → isTruncatedFun k f → isTruncatedFun k g → isTruncatedFun k (g ∘ f)
  isTruncatedFunComp k = {! !}

  isTruncatedFunSuc : ∀ k (f : A → B) → (∀ x y → isTruncatedFun k (cong {x = x} {y = y} f)) → isTruncatedFun (suc k) f
  isTruncatedFunSuc k f is-trunc-cong-f = {! !}

  isoAdjointExt : (f : Iso A B) (g : A → C) (h : B → C) → h ≡ g ∘ (f .Iso.inv) → h ∘ (f .Iso.fun) ≡ g
  isoAdjointExt f g h p = funExt λ a → funExt⁻ p _ ∙ cong g (f .Iso.leftInv a)


module _ {ℓB} {B : Type ℓB}
  (is-gpd-B : isGroupoid B)
  where
  private
    curryFiber2 : ∀ {f : 𝔹 → B} {b₀} {ℓP} {P : (x y : fiber f b₀) → Type ℓP} → ((x y : 𝔹) → (p : f x ≡ b₀) (q : f y ≡ b₀) → P (x , p) (y , q)) → (x y : fiber f b₀) → P x y
    curryFiber2 h (x , p) (y , q) = h x y p q

    unique : (b₀ : B) (φ : (g : G) → b₀ ≡ b₀) → (pres· : ∀ g h → compSquareFiller (φ g) (φ h) (φ $ g · h)) → isTruncatedFun 1 φ → isTruncatedFun 2 (Delooping.rec is-gpd-B b₀ φ pres·)
    unique b₀ φ pres· trunc-φ = isTruncatedFunSuc 1 f is-prop-trunc-f where
      f = Delooping.rec is-gpd-B b₀ φ pres·

      comm-lemma' : φ ≡ cong (Delooping.rec is-gpd-B b₀ φ pres·) ∘ decode {y = 𝔹.⋆}
      comm-lemma' = refl

      comm-lemma : φ ∘ encode {y = 𝔹.⋆} ≡ cong (Delooping.rec is-gpd-B b₀ φ pres·)
      comm-lemma = isoAdjointExt encodeDecodeIso _ _ comm-lemma'

      is-prop-trunc-φ∘encode : isTruncatedFun 1 (φ ∘ encode)
      is-prop-trunc-φ∘encode = isTruncatedFunComp 1 {! !} trunc-φ

      is-prop-trunc-f : (x y : 𝔹) → isTruncatedFun 1 (cong {x = x} {y = y} f)
      is-prop-trunc-f = Delooping.elimProp2 {! !} (subst (isTruncatedFun 1) comm-lemma is-prop-trunc-φ∘encode)

    lemma : (f : 𝔹 → B) → hasPropFibers (cong {x = 𝔹.⋆} {y = 𝔹.⋆} f) → ∀ x y → hasPropFibers (cong {x = x} {y = y} f)
    lemma f prop-fib = Delooping.elimProp2 {!λ _ _ → isPropHasPropFibers !} {! !}

  rec2TruncatedFunSuc : (f : 𝔹 → B) → hasPropFibers (cong {x = 𝔹.⋆} {y = 𝔹.⋆} f) → isTruncatedFun 2 f
  rec2TruncatedFunSuc f is-prop-trunc-f =
    let (x₀ , φ , φ-comp) = invEq (recEquiv {X = _ , is-gpd-B}) f
    in subst (isTruncatedFun 2) {! !} (unique x₀ φ φ-comp {! !})

recTruncatedFunSuc : ∀ {ℓX} {X : Type ℓX}
  → isGroupoid X
  → (k : HLevel) (f : 𝔹 → X)
  → isTruncatedFun k (cong {x = 𝔹.⋆} {y = 𝔹.⋆} f)
  → isTruncatedFun (suc k) f
recTruncatedFunSuc is-gpd-X k f trunc-cong-f x = {! !}
