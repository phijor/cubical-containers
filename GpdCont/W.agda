{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module GpdCont.W where

open import GpdCont.Prelude
open import GpdCont.HomotopySet using (SubSet)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.W.W public
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
import      Cubical.Data.Sum as Sum

W⁺ : ∀ {ℓA ℓB} (A : Type ℓA) (B : A → Type ℓB) → Type _
W⁺ A B = Σ[ a ∈ A ] (B a → W A B)

module _ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} where
  shape : W A B → A
  shape (sup-W s _) = s

  sub : (x : W A B) → B (shape x) → W A B
  sub (sup-W _ x) = x

  WRec : ∀ {ℓ} {M : Type ℓ}
    → (f : (a : A) → (B a → M) → M)
    → W A B → M
  WRec f (sup-W a x) = f a λ b → WRec f (x b)

  WIndExplicit : ∀ {ℓ} {M : W A B → Type ℓ}
    → (sup* : (a : A) → (t : B a → W A B) → ((b : B a) → (M (t b))) → M (sup-W a t))
    → (w : W A B) → M w
  WIndExplicit {M} sup* (sup-W a t) = sup* a t λ b → WIndExplicit {M = M} sup* (t b)

  unfoldWIso : Iso (W A B) (W⁺ A B)
  unfoldWIso .Iso.fun (sup-W s t) = s , t
  unfoldWIso .Iso.inv = uncurry sup-W
  unfoldWIso .Iso.rightInv _ = refl
  unfoldWIso .Iso.leftInv (sup-W _ _) = refl

  module WPath where
    shapePath : (x y : W A B) → Type _
    shapePath x y = shape x ≡ shape y

    subPath : (x y : W A B) → shapePath x y → Type _
    subPath x y p = PathP (λ i → B (p i) → W A B) (sub x) (sub y)

    proj : ∀ {a₀ a₁ : A} {t₀ : B a₀ → W A B} {t₁ : B a₁ → W A B}
      → (Σ[ p ∈ a₀ ≡ a₁ ] PathP (λ i → B (p i) → W A B) t₀ t₁)
      → sup-W a₀ t₀ ≡ sup-W a₁ t₁
    proj (p , q) i = sup-W (p i) (q i)

    Cover : (x y : W A B) → Type _
    Cover x y = Σ[ p ∈ shapePath x y ] subPath x y p

    encode : (x y : W A B) → x ≡ y → Cover x y
    encode x y p .fst = cong shape p
    encode x y p .snd = cong sub p

    decode : (x y : W A B) → Cover x y → x ≡ y
    decode x@(sup-W sx tx) y@(sup-W sy ty) (p , q) = λ i → sup-W (p i) (q i)

    encode-decode : ∀ x y → (c : Cover x y) → encode x y (decode x y c) ≡ c
    encode-decode (sup-W _ _) (sup-W _ _) _ = refl

    decode-encode : ∀ x y → (p : x ≡ y) → decode x y (encode x y p) ≡ p
    decode-encode x@(sup-W sx tx) y = J (λ y p → decode x y (encode x y p) ≡ p) refl

    encodeIso : (x y : W A B) → Iso (x ≡ y) (Cover x y)
    encodeIso x y .Iso.fun = encode x y
    encodeIso x y .Iso.inv = decode x y
    encodeIso x y .Iso.rightInv = encode-decode x y
    encodeIso x y .Iso.leftInv = decode-encode x y

    isPropW : isProp A → isProp (W A B)
    isPropW is-prop-A (sup-W sx tx) (sup-W sy ty) =
      cong₂ sup-W
        (is-prop-A sx sy)
        (toPathP (funExt λ b → isPropW is-prop-A _ (ty b)))

    isOfHLevelPredCover : (n : HLevel) → isOfHLevel (suc n) A → (x y : W A B) → isOfHLevel n (Cover x y)
    isOfHLevelSucW : (n : HLevel) → isOfHLevel (suc n) A → isOfHLevel (suc n) (W A B)

    isOfHLevelPredCover zero is-prop-A x y =
      isOfHLevelΣ 0
        (isProp→isContrPath is-prop-A (shape x) (shape y))
        (λ p → isOfHLevelPathP' 0 (isProp→ (isPropW is-prop-A)) (sub x) (sub y))
    isOfHLevelPredCover n@(suc k) lvl-A x@(sup-W _ _) y@(sup-W _ _) =
      isOfHLevelΣ n
        (lvl-A (shape x) (shape y))
        (λ p → {! !})

    isOfHLevelSucW zero = isPropW
    isOfHLevelSucW n@(suc _) lvl-A = lemma where
      lemma : (x y : W A B) → isOfHLevel n (x ≡ y)
      lemma x y = isOfHLevelRetractFromIso n (encodeIso x y) (isOfHLevelPredCover n lvl-A x y)

    {-
    Cover' : (x y : W A B) → Type _
    Cover' x y = W (shapePath x y) (subPath x y)

    subPath' : (x y : W A B) (p : shapePath x y) → Type _
    subPath' x y p = Σ[ b₀ ∈ B (shape x) ] Σ[ b₁ ∈ B (shape y) ] PathP (λ i → B (p i)) b₀ b₁

    Cover'' : (x y : W A B) → Type _
    Cover'' x y = W (shapePath x y) (subPath' x y)

    encode'' : (x y : W A B) → x ≡ y → Cover'' x y
    decode'' : (x y : W A B) → Cover'' x y → x ≡ y

    encode'' (sup-W sx tx) (sup-W sy ty) p = sup-W (cong shape p) λ where
      (b₀ , b₁ , pᴰ) → {! cong sub p !}
    decode'' (sup-W sx tx) (sup-W sy ty) (sup-W p pᴰ) = cong₂ sup-W p {! !} where
      sub-path : PathP (λ i → B (p i) → W A B) tx ty
      sub-path i b = {! !}

    reflCover' : (x : W A B) → Cover' x x
    reflCover' (sup-W s t) = sup-W (refl′ s) λ t≡t → reflCover' {! !}

    encode' : (x y : W A B) → x ≡ y → Cover' x y
    encodeExt' : (x y : W A B) {p : shape x ≡ shape y}
      → (∀ b₀ b₁ → PathP (λ i → B (p i)) b₀ b₁ → Cover' (sub x b₀) (sub y b₁))
      → Cover' x y

    encode' x@(sup-W sx tx) y@(sup-W sy ty) p = sup-W shape-path sub-cover
      where
        shape-path : shapePath x y
        shape-path = cong shape p

        sub-cover-ext : (pᴰ : PathP (λ i → B (shape-path i) → W A B) tx ty)
          → (b₀ : B sx) (b₁ : B sy) → PathP (λ i → B (shape-path i)) b₀ b₁
          → Cover' (tx b₀) (ty b₁)
        sub-cover-ext pᴰ b₀ b₁ b₀≡b₁ = encode' (tx b₀) (ty b₁) (λ i → pᴰ i (b₀≡b₁ i))

        sub-cover : subPath x y shape-path → Cover' x y
        sub-cover pᴰ = encodeExt' x y (sub-cover-ext pᴰ)

    encodeExt' x y pᴰ = encode' x y {! !}

    decode' : (x y : W A B) → Cover' x y → x ≡ y
    decode' x@(sup-W sx tx) y@(sup-W sy ty) = {! !}
    -}

WOfHLevel : ∀ {ℓA ℓB} (n : HLevel) → (A : TypeOfHLevel ℓA (suc n)) → (B : ⟨ A ⟩ → Type ℓB) → TypeOfHLevel _ (suc n)
WOfHLevel n A B .fst = W ⟨ A ⟩ B
WOfHLevel n A B .snd = WPath.isOfHLevelSucW n (str A)

WSet : ∀ {ℓA ℓB} (A : hSet ℓA) → (B : ⟨ A ⟩ → Type ℓB) → hSet _
WSet = WOfHLevel 1

syntax WOfHLevel n A (λ a → B) = W[ n ∣ a ∈ A ] B

module _ {ℓA ℓB ℓP}
  (A : hSet ℓA)
  (B : ⟨ A ⟩ → Type ℓB)
  (P : ∀ {a} → (B a → ⟨ WSet A B ⟩) → hProp ℓP)
  where
  isIterated : ⟨ WSet A B ⟩ → hProp (ℓ-max ℓB ℓP)
  isIterated (sup-W a ws) .fst = ⟨ P ws ⟩ × ∀ b → ⟨ isIterated (ws b) ⟩
  isIterated (sup-W a ws) .snd = isProp× (str (P ws)) $ isPropΠ λ b → str (isIterated (ws b))

  WSubSet : hSet _
  WSubSet = SubSet (WSet A B) isIterated

WSubSetInd : ∀ {ℓA ℓB ℓP ℓX} {A : hSet ℓA} {B : ⟨ A ⟩ → Type ℓB} {P : ∀ {a} → (B a → ⟨ WSet A B ⟩) → hProp ℓP}
  → (X : ⟨ WSubSet A B P ⟩ → hSet ℓX)
  → ∀ w → ⟨ X w ⟩
WSubSetInd X (sup-W s ws , p , ps) = {! !}

record Fix {ℓ} (S : Type ℓ) (Q : S → Type ℓ) : Type (ℓ-suc ℓ) where
  field
    Carrier : Type ℓ
    fix : Carrier ≃ (Σ[ s ∈ S ] (Q s → Carrier))

  unShape : Carrier → S
  unShape = fst ∘ equivFun fix

  unPos : (c : Carrier) → Q (unShape c) → Carrier
  unPos = snd ∘ equivFun fix

fixW : ∀ {ℓ} (S : Type ℓ) (Q : S → Type ℓ) → Fix S Q
fixW S Q .Fix.Carrier = W S Q
fixW S Q .Fix.fix = isoToEquiv unfoldWIso

module _ {ℓ} {S : Type ℓ} {Q : S → Type ℓ} (φ : Fix S Q) where
  open Fix φ

  data Fixᴰ (P : S → Type ℓ) : Carrier → Type ℓ where
    here : {c : Carrier} → P (unShape c) → Fixᴰ P c
    there : {c : Carrier}
      → (q : Q (unShape c))
      → Fixᴰ P (unPos c q)
      → Fixᴰ P c

  private
    variable
      P : S → Type ℓ
      c : Carrier

  CoverFixᴰ : (x y : Fixᴰ P c) → Type ℓ
  CoverFixᴰ (here p₁) (here p₂) = p₁ ≡ p₂
  CoverFixᴰ (here _) (there _ _) = ⊥*
  CoverFixᴰ (there _ _) (here _) = ⊥*
  CoverFixᴰ {P} (there q₁ x) (there q₂ y) = Σ[ p ∈ (q₁ ≡ q₂) ] PathP (λ i → Fixᴰ P (unPos _ (p i))) x y

  encodeRefl : ∀ x → CoverFixᴰ {P} {c} x x
  encodeRefl (here x) = refl
  encodeRefl (there q x) .fst = refl
  encodeRefl (there q x) .snd = refl

  encode : (x y : Fixᴰ P c) → x ≡ y → CoverFixᴰ x y
  encode x y = J (λ y p → CoverFixᴰ x y) (encodeRefl x)

  decode : (x y : Fixᴰ P c) → CoverFixᴰ x y → x ≡ y
  decode (here x) (here y) p = cong here p
  decode (there q₁ x) (there q₂ y) p = cong₂ there (p .fst) (p .snd)

  encode-section : (x y : Fixᴰ P c) → section (encode x y) (decode x y)
  encode-section {P} {c} (here x) (here y) = J (λ y p → encode {P} {c} (here x) (here y) (decode (here x) (here y) p) ≡ p) (transportRefl refl)
  encode-section {P} {c} (there q₁ x) (there q₂ y) = uncurry {! J (λ q₂ p → (pᴰ : PathP (λ i → Fixᴰ P (unPos c (p i))) x y) → encode (there q₁ x) (there q₂ y) (λ i → there (p i) (pᴰ i)) ≡ (p , pᴰ)) !}

  encodeIso : (x y : Fixᴰ P c) → Iso (x ≡ y) (CoverFixᴰ x y)
  encodeIso x y .Iso.fun = encode x y
  encodeIso x y .Iso.inv = decode x y
  encodeIso x y .Iso.rightInv p = {! !}
  encodeIso x y .Iso.leftInv = {! !}

  isOfHLevelFixᴰ : ∀ {P} {c} → (n : HLevel) → (∀ s → isOfHLevel n (P s)) → isOfHLevel n (Fixᴰ P c)
  isOfHLevelFixᴰ {P} {c} n lvl-P = {!  !}

module _ {ℓ} {S : Type ℓ} {Q : S → Type ℓ} (P : S → Type ℓ) where
  open import Cubical.Data.Nat using (_+_)
  WFixᴰ : W S Q → Type ℓ
  WFixᴰ = Fixᴰ (fixW S Q) P

  WFixᴰΣ : W S Q → Type ℓ
  WFixᴰΣ (sup-W s ws) = P s Sum.⊎ (Σ[ q ∈ Q s ] WFixᴰΣ (ws q))

  WFixᴰIsoΣ : (w : W S Q) → Iso (WFixᴰ w) (WFixᴰΣ w)
  WFixᴰIsoΣ = WIndExplicit the-iso where
    module _ (s : S) (ws : Q s → W S Q) (rec-iso : ∀ q → Iso (WFixᴰ (ws q)) (WFixᴰΣ (ws q))) where
      the-iso : Iso _ _
      the-iso .Iso.fun (here p) = Sum.inl p
      the-iso .Iso.fun (there q fs) = Sum.inr (q , rec-iso q .Iso.fun fs)
      the-iso .Iso.inv (Sum.inl p) = here p
      the-iso .Iso.inv (Sum.inr (q , fs)) = there q (rec-iso q .Iso.inv fs)
      the-iso .Iso.rightInv (Sum.inl p) = refl
      the-iso .Iso.rightInv (Sum.inr (q , fs)) i = Sum.inr (q , rec-iso q .Iso.rightInv fs i)
      the-iso .Iso.leftInv (here p) = refl
      the-iso .Iso.leftInv (there q fs) i = there q (rec-iso q .Iso.leftInv fs i)

  isOfHLevelWFixᴰΣ : (n : HLevel)
    → (∀ s → isOfHLevel (2 + n) (P s))
    → (∀ s → isOfHLevel (2 + n) (Q s))
    → ∀ w → isOfHLevel (2 + n) (WFixᴰΣ w)
  isOfHLevelWFixᴰΣ n lvl-P lvl-Q (sup-W s ws) =
    Sum.isOfHLevel⊎ n
      (lvl-P s)
      (isOfHLevelΣ (2 + n)
        (lvl-Q s)
        (λ q → isOfHLevelWFixᴰΣ n lvl-P lvl-Q (ws q))
      )

  isOfHLevelWFixᴰ : (n : HLevel)
    → (∀ s → isOfHLevel (2 + n) (P s))
    → (∀ s → isOfHLevel (2 + n) (Q s))
    → ∀ w → isOfHLevel (2 + n) (WFixᴰ w)
  isOfHLevelWFixᴰ n lvl-P lvl-Q w = isOfHLevelRetractFromIso (2 + n) (WFixᴰIsoΣ w) (isOfHLevelWFixᴰΣ n lvl-P lvl-Q w)


  module _ (leaves : ∀ s → Iso (P s) (P s)) where
    permuteIsoWFixᴰ : ∀ w → Iso (WFixᴰ w) (WFixᴰ w)
    permuteIsoWFixᴰ = def where
      map : (f : ∀ s → P s → P s) → ∀ w → WFixᴰ w → WFixᴰ w
      map f w@(sup-W s ws) (here p) = here (f s p)
      map f w@(sup-W s ws) (there q path) = there q (map f (ws q) path)

      to : ∀ w → WFixᴰ w → WFixᴰ w
      to = map (Iso.fun ∘ leaves)

      from : ∀ w → WFixᴰ w → WFixᴰ w
      from = map (Iso.inv ∘ leaves)

      rinv : ∀ w → section (to w) (from w)
      rinv (sup-W s ws) (here p) = cong here (leaves s .Iso.rightInv p)
      rinv (sup-W s ws) (there q path) = cong (there q) (rinv (ws q) path)

      linv : ∀ w → retract (to w) (from w)
      linv (sup-W s ws) (here p) = cong here (leaves s .Iso.leftInv p)
      linv (sup-W s ws) (there q path) = cong (there q) (linv (ws q) path)

      def : ∀ w → Iso _ _
      def w .Iso.fun = to w
      def w .Iso.inv = from w
      def w .Iso.rightInv = rinv w
      def w .Iso.leftInv = linv w

    permuteWFixᴰ : ∀ w → WFixᴰ w ≃ WFixᴰ w
    permuteWFixᴰ w = isoToEquiv (permuteIsoWFixᴰ w)

module Connectivity where
  open import GpdCont.Connectivity

  open import Cubical.Homotopy.Connected
  open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
  open import Cubical.HITs.PropositionalTruncation.Monad
  import      Cubical.Data.Empty as Empty
  open import Cubical.Relation.Nullary using (¬_)

  private
    variable
      ℓA ℓB : Level
      A : Type ℓA
      B : A → Type ℓB

  module _ {A : Type ℓA} {B : A → Type ℓB} where
    hasLeaf : Type _
    hasLeaf = ∃[ a₀ ∈ A ] ¬ B a₀

    hasLeaf→isInhW : hasLeaf → ∥ W A B ∥₁
    hasLeaf→isInhW = PT.map λ { (a₀ , ¬b) → sup-W a₀ (rec ∘ ¬b) }

    frob : (∀ a → B a) → ¬ (W A B)
    frob f (sup-W a ws) = frob f (ws (f a))

  isConnectedW : ∀ {A : Type ℓA} {B : A → Type ℓB} (k : HLevel) → isConnected k A → isConnected k (W A B)
  isConnectedW⁺ : ∀ {A : Type ℓA} {B : A → Type ℓB} (k : HLevel) → isConnected k A → isConnected k (W⁺ A B)

  isConnectedW⁺ {A} {B} zero conn-A = isConnectedZero (W⁺ A B)
  isConnectedW⁺ {A} {B} (suc k) conn-A = isConnectedΣ (suc k) conn-A goal where
    module _ (a : A) where
      inh-sub : ∥ W A B ∥₁
      inh-sub = isConnectedSuc→merelyInh k {! !} -- (isConnectedW (suc k) conn-A)

      mere-section : ∥ (B a → W A B) ∥₁
      mere-section = do
        w ← inh-sub
        return $ const w

      lemma-ext : (f g : B a → W A B) → isConnected k (∀ b → f b ≡ g b)
      lemma-ext f g = AC→isConnectedΠ k {! !} (λ b → isConnectedPath k {! !} {! !} {! !})

      lemma : (f g : B a → W A B) → isConnected k (f ≡ g)
      lemma f g = isConnectedRetractFromIso k (invIso funExtIso) $ lemma-ext f g

      goal : isConnected (suc k) (B a → W A B)
      goal = merelyInh×isConnectedPath→isConnectedSuc k mere-section lemma

  isConnectedW {A} {B} k conn-A = isConnectedRetractFromIso k unfoldWIso $ isConnectedW⁺ k conn-A
