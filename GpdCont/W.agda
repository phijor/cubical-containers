{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module GpdCont.W where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.W.W public
open import Cubical.Data.Empty

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

    Cover' : (x y : W A B) → Type _
    Cover' x y = W (shapePath x y) {! !}

    toCover : ∀ x y → Cover' x y → Cover x y
    toCover x@(sup-W sx tx) y@(sup-W sy ty) (sup-W p pᴰ) = p , λ i b → {! toCover !}

    toCover' : ∀ x y → Cover x y → Cover' x y
    toCover' x@(sup-W sx tx) y@(sup-W sy ty) (p , q) = sup-W p λ ps → toCover' {! !} {! !} {! !}

    data Cover* : (x y : W A B) → Type (ℓ-max ℓA ℓB) where
      cover : ∀ {sx sy} {tx ty}
        → (sp : sx ≡ sy)
        → (∀ {bx : B sx} {by : B sy} → PathP (λ i → B (sp i)) bx by → Cover* (tx bx) (ty by))
        → Cover* (sup-W sx tx) (sup-W sy ty)

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

WOfHLevel : ∀ {ℓA ℓB} (n : HLevel) → (A : TypeOfHLevel ℓA (suc n)) → (B : ⟨ A ⟩ → Type ℓB) → TypeOfHLevel _ (suc n)
WOfHLevel n A B .fst = W ⟨ A ⟩ B
WOfHLevel n A B .snd = WPath.isOfHLevelSucW n (str A)

WSet : ∀ {ℓA ℓB} (A : hSet ℓA) → (B : ⟨ A ⟩ → Type ℓB) → hSet _
WSet = WOfHLevel 1

syntax WOfHLevel n A (λ a → B) = W[ n ∣ a ∈ A ] B

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
  WFixᴰ : W S Q → Type ℓ
  WFixᴰ = Fixᴰ (fixW S Q) P

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
