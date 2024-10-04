module GpdCont.GroupoidContainer.Examples where

open import GpdCont.Prelude
open import GpdCont.GroupoidContainer.Base
open import GpdCont.GroupoidContainer.Eval
open import GpdCont.GroupoidContainer.Morphism using () renaming (GContMorphism to Morphism)
open import GpdCont.Polynomial as Poly using (Polynomial ; poly⟨_,_⟩)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws as GL using ()
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path as Path using ()
open import Cubical.Foundations.Transport using (transport⁻)
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv using (funExtDep)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Nat as Nat using (ℕ)
open import Cubical.Data.Sigma as Sigma using (_×_)
open import Cubical.Data.Vec as Vec using (Vec ; [] ; _∷_)
open import Cubical.Data.Int as Int using (ℤ)

private
  module _ where
    private
      variable
        ℓ : Level
        A : Type ℓ

    _^_ : ∀ {x : A} → x ≡ x → (k : ℤ) → x ≡ x
    p ^ ℤ.pos zero = refl
    p ^ ℤ.pos (suc n) = (p ^ (ℤ.pos n)) ∙ p
    p ^ ℤ.negsuc zero = sym p
    p ^ ℤ.negsuc (suc n) = (p ^ ℤ.negsuc n) ∙ sym p

    iter-cong : ∀ (B : A → Type ℓ) → {x : A} (p : x ≡ x) → ∀ k → cong B (p ^ k) ≡ (cong B p) ^ k
    iter-cong B p (ℤ.pos zero) = refl
    iter-cong B p (ℤ.pos (suc n)) = GL.cong-∙ B (p ^ ℤ.pos n) p ∙ cong (_∙ cong B p) (iter-cong B p (ℤ.pos n))
    iter-cong B p (ℤ.negsuc zero) = refl
    iter-cong B p (ℤ.negsuc (suc n)) = GL.cong-∙ B (p ^ ℤ.negsuc n) (sym p) ∙ cong (_∙ sym (cong B p)) (iter-cong B p (ℤ.negsuc n))

  module S1 where
    open import Cubical.HITs.S1 public

    elimProp : ∀ {ℓ} {P : S¹ → Type ℓ} → (∀ x → isProp (P x)) → (P-base : P base) → ∀ x → P x
    elimProp is-prop-P P-base base = P-base
    elimProp is-prop-P P-base (loop i) = isProp→PathP (λ i → is-prop-P (loop i)) P-base P-base i

  open S1 using (S¹)

  module Modulo where
    open import Cubical.HITs.Modulo public
    open Nat using (_+_)

    elimProp : ∀ k {ℓ} {P : Modulo k → Type ℓ} → (∀ x → isProp (P x)) → (embed* : ∀ n → P (embed n)) → ∀ x → P x
    elimProp zero _ embed* (embed n) = embed* n
    elimProp (suc k) is-prop-P embed* (embed n) = embed* n
    elimProp (suc k) is-prop-P embed* (step n i) = isProp→PathP (λ i → is-prop-P (step n i)) (embed* n) (embed* (suc (k + n))) i

    Fin : (k : ℕ) → Type
    Fin zero = ⊥
    Fin (suc k) = Modulo (suc k)

    isSetFin : ∀ {k} → isSet (Fin k)
    isSetFin {k = zero} ()
    isSetFin {k = suc k} = isSetModulo

    shift-mod : ∀ {k} → Modulo k → Modulo k
    shift-mod (embed n) = embed (suc n)
    shift-mod {k} (step n i) = path i where
      path : embed (suc n) ≡ embed (suc (k + n))
      path = ztep (suc n) ∙ cong embed (Nat.+-suc k n)

    unshift-mod-suc : ∀ k → Modulo (suc k) → Modulo (suc k)
    unshift-mod-suc k (embed n) = embed (k + n)
    unshift-mod-suc k (step n i) = path i where
      path : embed (k + n) ≡ embed (k + suc (k + n))
      path = ztep {suc k} (k + n) ∙ cong embed (sym (Nat.+-suc k (k + n)))

    unshift-mod : ∀ {k} → Modulo k → Modulo k
    unshift-mod {k = zero} (embed n) = embed n
    unshift-mod {k = suc k} = unshift-mod-suc k

    shift : ∀ {k} → Fin k → Fin k
    shift {k = zero} ()
    shift {k = suc k} = shift-mod

    unshift : ∀ {k} → Fin k → Fin k
    unshift {k = zero} ()
    unshift {k = suc k} = unshift-mod-suc k

    shiftIso : ∀ k → Iso (Fin k) (Fin k)
    shiftIso k .Iso.fun = shift
    shiftIso k .Iso.inv = unshift
    shiftIso zero .Iso.rightInv ()
    shiftIso (suc k) .Iso.rightInv = elimProp (suc k) (λ _ → isSetModulo _ _) λ n → sym (step n)
    shiftIso zero .Iso.leftInv ()
    shiftIso (suc k) .Iso.leftInv = elimProp (suc k) (λ _ → isSetModulo _ _) λ n → cong embed (Nat.+-suc k n) ∙ sym (ztep {suc k} n)

    shiftEquiv : ∀ k → Fin k ≃ Fin k
    shiftEquiv k = isoToEquiv $ shiftIso k

    shiftPath : ∀ k → Fin k ≡ Fin k
    shiftPath k = ua $ shiftEquiv k

    intShiftPath : (n : ℤ) → ∀ k → Fin k ≡ Fin k
    intShiftPath n k = shiftPath k ^ n
    
  open Modulo using (Fin ; isSetFin)

module CyclicList where
  Shape : Type
  Shape = ℕ × S¹

  isGroupoidShape : isGroupoid Shape
  isGroupoidShape = isGroupoid× (isSet→isGroupoid Nat.isSetℕ) (S1.isGroupoidS¹)

  Sh : ℕ → S¹ → Type
  Sh n = S1.rec (Modulo.Fin n) (Modulo.shiftPath n)

  Pos : ℕ × S¹ → Type
  Pos = uncurry Sh

  isSetPos : ∀ s → isSet (Pos s)
  isSetPos = uncurry λ n → S1.elimProp (λ _ → isPropIsSet) (Modulo.isSetFin)

  congShLoop≡shiftPath : ∀ {n} k → cong (Sh n) (S1.intLoop k) ≡ Modulo.shiftPath n ^ k
  congShLoop≡shiftPath {n} k = cong (cong (Sh n)) (mangle k) ∙ iter-cong (Sh n) S¹.loop k where
    mangle : ∀ k → S1.intLoop k ≡ S¹.loop ^ k
    mangle (ℤ.pos zero) = refl
    mangle (ℤ.pos (suc n)) = cong (_∙ S¹.loop) (mangle (ℤ.pos n))
    mangle (ℤ.negsuc zero) = refl
    mangle (ℤ.negsuc (suc n)) = cong (_∙ sym S¹.loop) (mangle (ℤ.negsuc n))

  Mod : (n : ℕ) → Type _
  Mod n = fiber π S¹.base where
     π : Σ S¹ (Sh n) → S¹
     π = fst

  isGroupoidMod : ∀ n → isGroupoid (Mod n)
  isGroupoidMod n = isGroupoidΣ (isGroupoidΣ S1.isGroupoidS¹ λ x → isSet→isGroupoid $ isSetPos (n , x)) λ _ → isSet→isGroupoid (S1.isGroupoidS¹ _ _)

  ModPos : Σ ℕ Mod → Type
  ModPos = uncurry λ k → uncurry $ uncurry (S1.elim (Motive k) (base* k) (loop* k)) where module _ (k : ℕ) where
    Motive : (x : S¹) → Type _
    Motive x = (y : Sh k x) (p : x ≡ S¹.base) → Type

    base* : Fin k → S¹.base ≡ S¹.base → Type
    base* _ _ = Fin k

    loop-path : PathP (λ i → S¹.loop i ≡ S¹.base → Type) (λ _ → Fin k) (λ _ → Fin k)
    loop-path i p = Pos (k , p i)

    loop* : PathP (λ i → ua (Modulo.shiftEquiv k) i → S¹.loop i ≡ S¹.base → Type) base* base*
    loop* i _ = loop-path i

  isSetModPos : ∀ x → isSet (ModPos x)
  isSetModPos = uncurry λ k → uncurry $ uncurry (S1.elimProp (λ _ → isPropΠ2 λ _ _ → isPropIsSet) λ _ _ → isSetFin)


CyclicList : GCont ℓ-zero
CyclicList .GCont.Shape = CyclicList.Shape
CyclicList .GCont.Pos = CyclicList.Pos
CyclicList .GCont.is-groupoid-shape = CyclicList.isGroupoidShape
CyclicList .GCont.is-set-pos = CyclicList.isSetPos

private
  variable
    A : Type

  -- Vec3→FinVec : Vec A 3 → (Fin 3 → A)
  -- Vec3→FinVec {A} (x₀ ∷ x₁ ∷ x₂ ∷ []) = λ where
  --     (Modulo.embed n) → x n
  --     (Modulo.step n i) → refl {x = x n} i
  --   where
  --     x : ℕ → A
  --     x 0 = x₀
  --     x 1 = x₁
  --     x 2 = x₂
  --     x (suc (suc (suc n))) = x n

mkCyc : ∀ {n} → (Fin n → A) → ⟦ CyclicList ⟧ᵗ A
mkCyc v .shape = _ , S¹.base
mkCyc v .label = v

shiftPathExt : ∀ {n} (xs : Fin n → A) → mkCyc (Modulo.shift ⋆ xs) ≡ mkCyc xs
shiftPathExt {A} {n} xs = Poly.Polynomial≡ shape-path pos-path where
  shape-path : (n , S¹.base) ≡ (n , S¹.base)
  shape-path i = n , S¹.loop i

  pos-path : PathP (λ i → CyclicList.Pos (shape-path i) → A) (Modulo.shift ⋆ xs) xs
  pos-path = ua→ λ k → refl {x = xs (Modulo.shift k)}


CyclicListPathEquiv : ∀ {xs@(poly⟨ (m , s) , v ⟩) ys@(poly⟨ (n , t) , w ⟩) : ⟦ CyclicList ⟧ᵗ A}
  → (xs ≡ ys) ≃ (Σ[ len-path ∈ m ≡ n ] Σ[ circle-path ∈ s ≡ t ] PathP (λ i → CyclicList.Pos (len-path i , circle-path i) → A) v w)
CyclicListPathEquiv {A} {xs@(poly⟨ (m , s) , v ⟩)} {ys@(poly⟨ (n , t) , w ⟩)} =
  (xs ≡ ys) ≃⟨ Poly.Polynomial≡Equiv ⟩
  Σ[ shape-path ∈ (m , s) ≡ (n , t) ] (PathP (λ i → CyclicList.Pos (shape-path i) → A) v w) ≃⟨ invEquiv $ Sigma.Σ-cong-equiv-fst Sigma.ΣPath≃PathΣ ⟩
  Σ[ shape-path ∈ Σ (m ≡ n) _ ] PathP (λ i → CyclicList.Pos (shape-path .fst i , shape-path .snd i) → A) v w ≃⟨ Sigma.Σ-assoc-≃ ⟩
  Σ[ len-path ∈ m ≡ n ] Σ[ circle-path ∈ s ≡ t ] PathP (λ i → CyclicList.Pos (len-path i , circle-path i) → A) v w ≃∎

CyclicListShiftPathEquiv : ∀ {n} {xs ys : Fin n → A}
  → (mkCyc xs ≡ mkCyc ys) ≃ (Σ[ winding ∈ ℤ ] ((PathP (λ i → CyclicList.Pos (n , S1.intLoop winding i) → A) xs ys)))
CyclicListShiftPathEquiv {A} {n} {xs} {ys} =
  (mkCyc xs ≡ mkCyc ys) ≃⟨ CyclicListPathEquiv ⟩
  Σ[ r ∈ (n ≡ n) ] Σ[ loop ∈ S¹.base ≡ S¹.base ] (PathP (λ i → CyclicList.Pos (r i , loop i) → A) xs ys) ≃⟨ Sigma.Σ-contractFst isContr-n≡n ⟩
  Σ[ loop ∈ S¹.base ≡ S¹.base ] (PathP (λ i → CyclicList.Pos (n , loop i) → A) xs ys) ≃⟨ invEquiv $ Sigma.Σ-cong-equiv-fst ℤ≃ΩS¹ ⟩
  Σ[ winding ∈ ℤ ] ((PathP (λ i → CyclicList.Pos (n , S1.intLoop winding i) → A) xs ys)) ≃∎
  where
    isContr-n≡n : isContr (n ≡ n)
    isContr-n≡n = inhProp→isContr refl (Nat.isSetℕ n n)

    ℤ≃ΩS¹ : ℤ ≃ (S¹.base ≡ S¹.base)
    ℤ≃ΩS¹ = isoToEquiv $ invIso S1.ΩS¹Isoℤ

mkCycPath≃intShift : ∀ {n} {xs ys : Fin n → A}
  → (mkCyc xs ≡ mkCyc ys) ≃ (Σ[ winding ∈ ℤ ] xs ≡ ys ∘ transport (Modulo.intShiftPath winding n))
mkCycPath≃intShift {A} {n} {xs} {ys} =
  (mkCyc xs ≡ mkCyc ys) ≃⟨ CyclicListShiftPathEquiv ⟩
  Σ[ winding ∈ ℤ ] ((PathP (λ i → CyclicList.Pos (n , S1.intLoop winding i) → A) xs ys))
    ≃⟨ Sigma.Σ-cong-equiv-snd (λ z → pathToEquiv (Path.PathP≡Path (λ i → CyclicList.Pos (n , S1.intLoop z i) → A) _ _)) ⟩
  Σ[ winding ∈ ℤ ] (subst (λ s → CyclicList.Sh n s → A) (S1.intLoop winding) ) xs ≡ ys ≃⟨ Sigma.Σ-cong-equiv-snd step ⟩
  Σ[ winding ∈ ℤ ] xs ≡ ys ∘ transport (Modulo.intShiftPath winding n) ≃∎
  where module _ (k : ℤ) where
    subst-path : subst (λ s → CyclicList.Sh n s → A) (S1.intLoop k) xs ≡ xs ∘ subst (CyclicList.Sh n) (sym $ S1.intLoop k)
    subst-path = substCodomain (CyclicList.Sh n) (S1.intLoop k) xs

    shift-path : transport⁻ (cong (CyclicList.Sh n) $ S1.intLoop k) ≡ transport⁻ (Modulo.intShiftPath k n)
    shift-path = cong transport⁻ (CyclicList.congShLoop≡shiftPath k)

    step =
      (subst (λ s → CyclicList.Sh n s → A) (S1.intLoop k) xs ≡ ys)
        ≃⟨ pathToEquiv $ cong (_≡ ys) $ subst-path ∙ (cong (xs ∘_) shift-path) ⟩
      (xs ∘ transport⁻ (Modulo.intShiftPath k n) ≡ ys)
        ≃⟨ isoToEquiv Path.symIso ⟩
      (ys ≡ xs ∘ transport⁻ (Modulo.intShiftPath k n))
        ≃⟨ pathToEquiv $ cong (λ f → ys ≡ xs ∘ f) $ funExt (λ pos → sym $ transportRefl {A = Fin n} (transport⁻ (Modulo.intShiftPath k n) pos)) ⟩
      (ys ≡ xs ∘ invEq (pathToEquiv $ Modulo.intShiftPath k n))
        ≃⟨ preCompAdjointEquiv (pathToEquiv (Modulo.intShiftPath k n)) xs ys ⟩
      (ys ∘ transport (Modulo.intShiftPath k n) ≡ xs)
        ≃⟨ isoToEquiv Path.symIso ⟩
      (xs ≡ ys ∘ transport (Modulo.intShiftPath k n))
        ≃∎

module cyc3 (x₀ x₁ x₂ : A) where
  embed : ℕ → A
  embed 0 = x₀
  embed 1 = x₁
  embed 2 = x₂
  embed (suc (suc (suc n))) = embed n

  vec : Fin 3 → A
  vec (Modulo.embed n) = embed n
  vec (Modulo.step n i) = embed n

  ⦅_,_,_⦆ : ⟦ CyclicList ⟧ᵗ A
  ⦅_,_,_⦆ = mkCyc {n = 3} vec

open cyc3 using (⦅_,_,_⦆)

cyc-shift-embed : ∀ (x₀ x₁ x₂ : A) n → cyc3.embed x₀ x₁ x₂ n ≡ cyc3.embed x₂ x₀ x₁ (suc n)
cyc-shift-embed _ _ _ 0 = refl
cyc-shift-embed _ _ _ 1 = refl
cyc-shift-embed _ _ _ 2 = refl
cyc-shift-embed _ _ _ (suc (suc (suc n))) = cyc-shift-embed _ _ _ n

cyc-shift-compute : ∀ (x₀ x₁ x₂ : ℕ) → cyc3.vec x₀ x₁ x₂ ≡ cyc3.vec x₂ x₀ x₁ ∘ Modulo.shift
cyc-shift-compute x₀ x₁ x₂ = funExt (Modulo.elimProp 3 (λ _ → Nat.isSetℕ _ _) $ cyc-shift-embed x₀ x₁ x₂)

example-path : ⦅ 1 , 2 , 3 ⦆ ≡ ⦅ 3 , 1 , 2 ⦆
example-path = cong (mkCyc {A = ℕ}) (cyc-shift-compute 1 2 3) ∙ shiftPathExt {A = ℕ} {n = 3} (cyc3.vec 3 1 2)

example-path' : ⦅ 1 , 2 , 3 ⦆ ≡ ⦅ 3 , 1 , 2 ⦆
example-path' = invEq (mkCycPath≃intShift {A = ℕ} {xs = cyc3.vec 1 2 3} {ys = cyc3.vec 3 1 2}) (1 , compute) where
  compute : cyc3.vec 1 2 3 ≡ cyc3.vec 3 1 2 ∘ transport (refl ∙ Modulo.shiftPath 3)
  compute =
    cyc3.vec 1 2 3 ≡⟨ cyc-shift-compute 1 2 3 ⟩
    cyc3.vec 3 1 2 ∘ Modulo.shift ≡[ i ]⟨ cyc3.vec 3 1 2 ∘ {! !} ⟩
    cyc3.vec 3 1 2 ∘ transport (Modulo.shiftPath 3) ≡⟨ cong (λ p → cyc3.vec 3 1 2 ∘ transport p) (GL.lUnit (Modulo.shiftPath 3)) ⟩
    cyc3.vec 3 1 2 ∘ transport (refl ∙ Modulo.shiftPath 3) ∎

module ModList where
  ModCyc : GCont _
  ModCyc .GCont.Shape = Σ ℕ CyclicList.Mod
  ModCyc .GCont.Pos = CyclicList.ModPos
  ModCyc .GCont.is-groupoid-shape = isGroupoidΣ (isSet→isGroupoid Nat.isSetℕ) CyclicList.isGroupoidMod
  ModCyc .GCont.is-set-pos = CyclicList.isSetModPos

  μ : Morphism CyclicList ModCyc
  μ = def where
    μ-shape : ∀ {n} → S¹ → CyclicList.Mod n
    μ-shape {n = zero} x .fst = x , {! !}
    μ-shape {n = zero} x .snd = {! !}
    μ-shape {n = suc n} S¹.base = (S¹.base , {! !}) , refl
    μ-shape {n = suc n} (S¹.loop i) = {! !}
    -- μ-shape {n = suc n} = S1.rec base* λ i → (S¹.loop i , ua-gluePath (Modulo.shiftEquiv (suc n)) {x = Modulo.embed 0} {! !} i) , {! !} where
    --   base* : CyclicList.Mod (suc n)
    --   base* .fst = S1.base , Modulo.embed 0
    --   base* .snd = refl

    def : Morphism _ _
    def .Morphism.shape-mor = Sigma.map-snd μ-shape
    def .Morphism.pos-path = {! !}


-- module MVP (A : Type) where
--   data Hmm (a : A) : Type where
--     pt : Hmm a
--     loop : pt ≡ pt

  -- boom : ∀ a (e : Hmm a ≃ Hmm a) → transport (ua e) ≡ equivFun e
  -- boom a e = refl