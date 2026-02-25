{-# OPTIONS --lossy-unification #-}

open import GpdCont.Prelude
open import Cubical.Algebra.Group.Base using (GroupStr ; Group)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom ; GroupEquiv)
open import Cubical.Algebra.Group.MorphismProperties using (isPropIsGroupHom ; makeIsGroupHom ; invGroupEquiv ; GroupEquiv→GroupHom)
open import Cubical.Algebra.Group.GroupPath using (uaGroup)
open import Cubical.Algebra.SymmetricGroup using (Symmetric-Group)

module GpdCont.Delooping.Properties {ℓ} (G : Group ℓ) where

open import GpdCont.Group.Solve using (solveGroup)

private
  module G where
    open GroupStr (str G) public
    open GroupTheory G public

    reassoc : (g g′ h : ⟨ G ⟩) → g · (g′ · h · g) · g′ ≡ (g · g′) · h · (g · g′)
    reassoc = solveGroup G

    ·IdLR : (h : ⟨ G ⟩) → 1g · h · 1g ≡ h
    ·IdLR h = cong (1g ·_) (·IdR h) ∙ ·IdL h


  open G using (_·_ ; inv)

open import GpdCont.Experimental.Groups.Base using () renaming (GroupStr to hGroupStr)
open import GpdCont.Delooping.Base G as Delooping using (𝔹)
open import GpdCont.Connectivity using (isPathConnected ; isPathConnected→merePath)
open import GpdCont.Univalence using (ua→)

import GpdCont.Group.FundamentalGroup as FundamentalGroup

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties hiding (conjugatePathEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPath→Square)
open import Cubical.Foundations.Univalence hiding (elimIso ; ua→)
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding

isPropSetTruncDelooping : isProp ∥ 𝔹 ∥₂
isPropSetTruncDelooping = ST.elim2 (λ s t → ST.isSetPathImplicit) conn-lemma where
  conn-lemma : (s t : 𝔹) → ST.∣ s ∣₂ ≡ ST.∣ t ∣₂
  conn-lemma = Delooping.elimProp {B = λ s → (t : 𝔹) → ST.∣ s ∣₂ ≡ ST.∣ t ∣₂}
    (λ s → isPropΠ λ t → ST.isSetSetTrunc _ _)
    (Delooping.elimProp (λ t → ST.isSetSetTrunc _ _) $ refl {x = ST.∣ Delooping.⋆ ∣₂})

isConnectedDelooping : isContr ∥ 𝔹 ∥₂
isConnectedDelooping = inhProp→isContr ST.∣ 𝔹.⋆ ∣₂ isPropSetTruncDelooping

merePath : (x y : 𝔹) → ∥ x ≡ y ∥₁
merePath = isPathConnected→merePath isConnectedDelooping

deloopingGroupStr : hGroupStr 𝔹
deloopingGroupStr .hGroupStr.is-connected = isConnectedDelooping
deloopingGroupStr .hGroupStr.is-groupoid = Delooping.isGroupoid𝔹
deloopingGroupStr .hGroupStr.pt = Delooping.⋆

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

isPropDeloopingSquare :
  {x₀₀ x₀₁ : 𝔹} {x₀₋ : x₀₀ ≡ x₀₁}
  {x₁₀ x₁₁ : 𝔹} {x₁₋ : x₁₀ ≡ x₁₁}
  {x₋₀ : x₀₀ ≡ x₁₀} {x₋₁ : x₀₁ ≡ x₁₁}
  → isProp (Square x₀₋ x₁₋ x₋₀ x₋₁)
isPropDeloopingSquare = isGroupoid→isPropSquare Delooping.isGroupoid𝔹

private
  conjugate : (g : ⟨ G ⟩) → ⟨ G ⟩ → ⟨ G ⟩
  conjugate g h = inv g · h · g

  conjugateIso : (g : ⟨ G ⟩) → Iso ⟨ G ⟩ ⟨ G ⟩
  conjugateIso g .Iso.fun = conjugate g
  conjugateIso g .Iso.inv = conjugate (inv g)
  conjugateIso g .Iso.sec h =
    inv g · (inv (inv g) · h · inv g) · g ≡[ i ]⟨ inv g · (G.invInv g i · h · inv g) · g ⟩
    inv g · (g · (h · inv g)) · g ≡⟨ G.reassoc (inv g) g h ⟩
    (inv g · g) · h · (inv g · g) ≡⟨ cong (λ - → - · h · -) (G.·InvL g) ⟩
    G.1g · h · G.1g ≡⟨ G.·IdLR h ⟩
    h ∎
  conjugateIso g .Iso.ret h =
    inv (inv g) · (inv g · h · g) · inv g ≡⟨ cong (_· (inv g · h · g) · inv g) (G.invInv g) ⟩
    g · (inv g · h · g) · inv g ≡⟨ G.reassoc g (inv g) h ⟩
    (g · inv g) · h · (g · inv g) ≡⟨ cong (λ - → - · h · -) (G.·InvR g) ⟩
    G.1g · h · G.1g ≡⟨ G.·IdLR h ⟩
    h ∎

  conjugateEquiv : (g : ⟨ G ⟩) → ⟨ G ⟩ ≃ ⟨ G ⟩
  conjugateEquiv g = isoToEquiv $ conjugateIso g

  conjugatePath : (g : ⟨ G ⟩) → ⟨ G ⟩ ≡ ⟨ G ⟩
  conjugatePath g = ua $ conjugateEquiv g

  conjugatePathFiller : ∀ g h → compSquareFiller (conjugatePath g) (conjugatePath h) (conjugatePath $ g · h)
  conjugatePathFiller g h = coerceCompSquareFiller $
    ua (conjugateEquiv g) ∙ ua (conjugateEquiv h) ≡⟨ sym (uaCompEquiv _ _) ⟩
    ua (conjugateEquiv g ∙ₑ conjugateEquiv h) ≡⟨ cong ua $ equivEq $ funExt shuffle ⟩
    ua (conjugateEquiv $ g · h) ∎
    where
      shuffle : ∀ x → inv h · (inv g · x · g) · h ≡ inv (g · h) · x · g · h
      shuffle x =
        inv h · (inv g · x · g) · h ≡⟨ lemma₁ (inv h) (inv g) x g h ⟩
        (inv h · inv g) · x · g · h ≡⟨ cong (λ - → - · x · g · h) (sym $ G.invDistr g h) ⟩
        inv (g · h) · x · g · h ∎
        where
          lemma₁ : (h⁻¹ g⁻¹ x g h : ⟨ G ⟩) → h⁻¹ · (g⁻¹ · x · g) · h ≡ (h⁻¹ · g⁻¹) · x · g · h
          lemma₁ = solveGroup G

  mulRightIso : (g : ⟨ G ⟩) → Iso ⟨ G ⟩ ⟨ G ⟩
  mulRightIso g .Iso.fun = _· g
  mulRightIso g .Iso.inv = _· (inv g)
  mulRightIso g .Iso.sec h = sym (G.·Assoc h (inv g) g) ∙ cong (h ·_) (G.·InvL g) ∙ G.·IdR h
  mulRightIso g .Iso.ret h = sym (G.·Assoc h g (inv g)) ∙ cong (h ·_) (G.·InvR g) ∙ G.·IdR h

  mulRightEquiv : (g : ⟨ G ⟩) → ⟨ G ⟩ ≃ ⟨ G ⟩
  mulRightEquiv g = isoToEquiv $ mulRightIso g

  mulRightPath : (g : ⟨ G ⟩) → ⟨ G ⟩ ≡ ⟨ G ⟩
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
  Code[⋆≡⋆] .fst = ⟨ G ⟩
  Code[⋆≡⋆] .snd = G.is-set

  Code[⋆≡_] : ⟨ G ⟩ → Code[⋆≡⋆] ≡ Code[⋆≡⋆]
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
encodeDecodeIso .Iso.sec = encode-decode _
encodeDecodeIso .Iso.ret = decode-encode

encodeDecode : ∀ {y} → (𝔹.⋆ ≡ y) ≃ ⟨ Code y ⟩
encodeDecode = isoToEquiv encodeDecodeIso

ΩDelooping≃ : (𝔹.⋆ ≡ 𝔹.⋆) ≃ ⟨ G ⟩
ΩDelooping≃ = encodeDecode {y = 𝔹.⋆}

unloop : 𝔹.⋆ ≡ 𝔹.⋆ → ⟨ G ⟩
unloop = equivFun ΩDelooping≃

loopEquiv : ⟨ G ⟩ ≃ (𝔹.⋆ ≡ 𝔹.⋆)
loopEquiv = invEquiv ΩDelooping≃

isEquivLoop : isEquiv 𝔹.loop
isEquivLoop = equivIsEquiv loopEquiv

π₁ : (x₀ : 𝔹) → Group _
π₁ = FundamentalGroup.π₁ (𝔹 , 𝔹.isGroupoid𝔹)

private
  π₁𝔹 : Group _
  π₁𝔹 = π₁ 𝔹.⋆

conjugatePathEquiv : {x₀ x₁ : 𝔹} → x₀ ≡ x₁ → GroupEquiv (π₁ x₀) (π₁ x₁)
conjugatePathEquiv = FundamentalGroup.conjugateGroupEquiv (𝔹 , 𝔹.isGroupoid𝔹)

conjugatePathHom : {x₀ x₁ : 𝔹} → x₀ ≡ x₁ → GroupHom (π₁ x₀) (π₁ x₁)
conjugatePathHom p = GroupEquiv→GroupHom $ conjugatePathEquiv p

loopHom : GroupHom G π₁𝔹
loopHom .fst = 𝔹.loop
loopHom .snd .IsGroupHom.pres· g h = sym $ Delooping.loop-∙ g h
loopHom .snd .IsGroupHom.pres1 = Delooping.loop-1
loopHom .snd .IsGroupHom.presinv = Delooping.loop-inv

loopGroupEquiv : GroupEquiv G π₁𝔹
loopGroupEquiv .fst = loopEquiv
loopGroupEquiv .snd = loopHom .snd

unloopGroupEquiv : GroupEquiv π₁𝔹 G
unloopGroupEquiv = invGroupEquiv loopGroupEquiv

unloopGroupHom : GroupHom π₁𝔹 G
unloopGroupHom = GroupEquiv→GroupHom unloopGroupEquiv

_ : unloopGroupHom .fst ≡ unloop
_ = refl

elimSetIso : ∀ {ℓB} {B : 𝔹 → Type ℓB}
  → (∀ x → isSet (B x))
  → Iso (Σ[ b₀ ∈ B 𝔹.⋆ ] (∀ g → PathP (λ i → B (𝔹.loop g i)) b₀ b₀)) (∀ x → B x)
elimSetIso is-set-B .Iso.fun = uncurry $ Delooping.elimSet is-set-B
elimSetIso is-set-B .Iso.inv b = b 𝔹.⋆ , cong b ∘ 𝔹.loop
elimSetIso is-set-B .Iso.sec b = funExt (Delooping.elimProp (λ _ → isOfHLevelPathP' 1 (is-set-B _) _ _) refl)
elimSetIso is-set-B .Iso.ret (b₀ , p) = refl

elimSetEquiv : ∀ {ℓB} {B : 𝔹 → Type ℓB}
  → (∀ x → isSet (B x))
  → (Σ[ b₀ ∈ B 𝔹.⋆ ] (∀ g → PathP (λ i → B (𝔹.loop g i)) b₀ b₀)) ≃ (∀ x → B x)
elimSetEquiv = isoToEquiv ∘ elimSetIso

elimPropIso : ∀ {ℓB} {B : 𝔹 → Type ℓB}
  → (∀ x → isProp (B x))
  → Iso (B 𝔹.⋆) (∀ x → B x)
elimPropIso is-prop-B .Iso.fun = Delooping.elimProp is-prop-B
elimPropIso is-prop-B .Iso.inv f = f 𝔹.⋆
elimPropIso is-prop-B .Iso.sec f = funExt λ x → is-prop-B _ _ (f x)
elimPropIso is-prop-B .Iso.ret _ = refl

elimPropEquiv : ∀ {ℓB} {B : 𝔹 → Type ℓB}
  → (∀ x → isProp (B x))
  → (B 𝔹.⋆) ≃ (∀ x → B x)
elimPropEquiv = isoToEquiv ∘ elimPropIso

recEquiv : ∀ {ℓX} {X : hGroupoid ℓX}
  → (Σ[ x₀ ∈ ⟨ X ⟩ ] Σ[ φ ∈ (⟨ G ⟩ → x₀ ≡ x₀) ] ∀ g h → compSquareFiller (φ g) (φ h) (φ $ g · h)) ≃ (𝔹 → ⟨ X ⟩)
recEquiv {X = (X , is-gpd-X)} = rec-equiv , is-equiv where
  open IsGroupHom using (pres·)
  rec-equiv : _ → _
  rec-equiv (x₀ , φ , φ-hom) = Delooping.rec is-gpd-X x₀ φ φ-hom

  rec-inv : (𝔹 → X) → (Σ[ x₀ ∈ X ] Σ[ φ ∈ (⟨ G ⟩ → x₀ ≡ x₀) ] ∀ g h → compSquareFiller (φ g) (φ h) (φ $ g · h))
  rec-inv f .fst = f 𝔹.⋆
  rec-inv f .snd .fst = cong f ∘ 𝔹.loop
  rec-inv f .snd .snd = λ g h i j → f (Delooping.loop-comp g h i j)

  recIso : Iso _ _
  recIso .Iso.fun = rec-equiv
  recIso .Iso.inv = rec-inv
  recIso .Iso.sec f = funExt (Delooping.elim (λ _ → isSet→isGroupoid (is-gpd-X _ _)) refl (λ g i j → f (𝔹.loop g i)) λ g h i j k → f (𝔹.loop-comp g h i j))
  recIso .Iso.ret (x₀ , φ , φ-comp) = refl

  is-equiv : isEquiv rec-equiv
  is-equiv = isoToIsEquiv recIso

recEquivHom : ∀ {ℓX} {X : hGroupoid ℓX}
  → (Σ[ x₀ ∈ ⟨ X ⟩ ] GroupHom G (FundamentalGroup.π₁ X x₀)) ≃ (𝔹 → ⟨ X ⟩)
recEquivHom {X} = Σ-cong-equiv-snd (λ x₀ → Σ-cong-equiv-snd $ lemma x₀) ∙ₑ recEquiv where
  lemma : ∀ x₀ (φ : ⟨ G ⟩ → x₀ ≡ x₀) →
    IsGroupHom (str G) φ (FundamentalGroup.π₁ X x₀ .snd)
      ≃
    ((g h : ⟨ G ⟩) → compSquareFiller (φ g) (φ h) (φ $ g · h))
  lemma x₀ φ = propBiimpl→Equiv (isPropIsGroupHom _ _) (isPropΠ2 (λ g h → isGroupoid→isPropSquare (str X)))
    (λ is-hom g h → coerceCompSquareFiller (sym $ is-hom .IsGroupHom.pres· g h))
    (λ mk-comp-sq → makeIsGroupHom λ g h → sym (compSquareFillerUnique (mk-comp-sq g h)))

module _ {ℓ'} {B : 𝔹 → Type ℓ'} where
  cong⋆ : {f g : ∀ x → B x} (p : f ≡ g) → PathP (λ i → B 𝔹.⋆) (f 𝔹.⋆) (g 𝔹.⋆)
  cong⋆ = cong (λ f → f 𝔹.⋆)

  cong⋆-∙ : {f g h : ∀ x → B x} (p : f ≡ g) (q : g ≡ h) → cong⋆ (p ∙ q) ≡ cong⋆ p ∙ cong⋆ q
  cong⋆-∙ = cong-∙ (λ f → f 𝔹.⋆)
