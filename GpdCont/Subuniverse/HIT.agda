open import GpdCont.Prelude

open import GpdCont.HomotopySet

module GpdCont.Subuniverse.HIT {ℓ} (U : hSet ℓ) (El : ⟨ U ⟩ → hSet ℓ) where

open import GpdCont.Subuniverse U El hiding (rec ; elimProp)
open import GpdCont.Prelude.Square
open import GpdCont.Equiv
open import GpdCont.Univalence

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise using (fundamentalTheoremOfId)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma


data Subᵁ : Type ℓ where
  codeᵁ : ⟨ U ⟩ → Subᵁ
  linkᵁ : ∀ {a b : ⟨ U ⟩} → ⟨ El a ⟩ ≃ ⟨ El b ⟩ → codeᵁ a ≡ codeᵁ b
  compᵁ : ∀ {a b c}
    → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩)
    → (f : ⟨ El b ⟩ ≃ ⟨ El c ⟩)
    → Square (linkᵁ e) (linkᵁ (e ∙ₑ f)) (refl′ (codeᵁ a)) (linkᵁ f)
  isGroupoidSubᵁ : isGroupoid Subᵁ

idᵁ : (a : ⟨ U ⟩) → linkᵁ (idEquiv ⟨ El a ⟩) ≡ refl′ (codeᵁ a)
idᵁ a = λ i j → hcomp (sides i j) (base i j) where
  1e : _ ≃ _
  1e = idEquiv ⟨ El a ⟩

  lhs : Square refl (sym $ linkᵁ 1e) (linkᵁ $ 1e ∙ₑ 1e) (linkᵁ 1e)
  lhs j k = compᵁ 1e 1e (~ k) j

  rhs : Square refl (sym $ linkᵁ 1e) (linkᵁ 1e) refl
  rhs j k = linkᵁ 1e (j ∧ ~ k)

  sides : (i j k : I) → Partial (∂² i j) Subᵁ
  sides i j k (i = i0) = lhs j k
  sides i j k (i = i1) = rhs j k
  sides i j k (j = i0) = codeᵁ a
  sides i j k (j = i1) = linkᵁ 1e (~ k)

  base : linkᵁ (1e ∙ₑ 1e) ≡ linkᵁ 1e
  base = cong linkᵁ $ equivEq refl

rec : ∀ {ℓB} {B : Type ℓB}
  → isGroupoid B
  → (code* : ⟨ U ⟩ → B)
  → (link* : ∀ {a b} → ⟨ El a ⟩ ≃ ⟨ El b ⟩ → code* a ≡ code* b)
  → (comp* : ∀ {a b c}
      → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩)
      → (f : ⟨ El b ⟩ ≃ ⟨ El c ⟩)
      → Square (link* e) (link* (e ∙ₑ f)) (refl′ (code* a)) (link* f)
    )
  → Subᵁ → B
rec {B} is-groupoid-B code* link* comp* = go where
  go : Subᵁ → B
  go (codeᵁ a) = code* a
  go (linkᵁ e i) = link* e i
  go (compᵁ e f i j) = comp* e f i j
  go (isGroupoidSubᵁ x y p q r s i j k) = is-groupoid-B
    (go x) (go y)
    (cong go p) (cong go q)
    (cong (cong go) r) (cong (cong go) s)
    i j k

elim : ∀ {ℓB} {B : Subᵁ → Type ℓB}
  → (∀ X → isGroupoid (B X))
  → (code* : (a : ⟨ U ⟩) → B (codeᵁ a))
  → (link* : ∀ {a b} → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩) → PathP (λ i → B (linkᵁ e i)) (code* a) (code* b))
  → (comp* : ∀ {a b c}
      → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩)
      → (f : ⟨ El b ⟩ ≃ ⟨ El c ⟩)
      → SquareP (λ i j → B (compᵁ e f i j)) (link* e) (link* (e ∙ₑ f)) (refl′ (code* a)) (link* f)
    )
  → (X : Subᵁ) → B X
elim {B} is-groupoid-B code* link* comp* = go where
  is-groupoid-B* : isOfHLevelDep 3 B
  is-groupoid-B* {(x)} {(y)} = isOfHLevel→isOfHLevelDep 3 is-groupoid-B {x} {y}

  go : (X : Subᵁ) → B X
  go (codeᵁ a) = code* a
  go (linkᵁ e i) = link* e i
  go (compᵁ e f i j) = comp* e f i j
  go (isGroupoidSubᵁ X Y p q r s i j k) = is-groupoid-B* (go X) (go Y) (cong go p) (cong go q) (cong (cong go) r) (cong (cong go) s) (isGroupoidSubᵁ X Y p q r s) i j k

elimSet : ∀ {ℓB} {B : Subᵁ → Type ℓB}
  → (∀ X → isSet (B X))
  → (code* : (a : ⟨ U ⟩) → B (codeᵁ a))
  → (link* : ∀ {a b} → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩) → PathP (λ i → B (linkᵁ e i)) (code* a) (code* b))
  → (X : Subᵁ) → B X
elimSet {B} is-set-B code* link* = elim {B = B} (isSet→isGroupoid ∘ is-set-B) code* link* comp* where
  comp* : ∀ {a b c}
    → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩)
    → (f : ⟨ El b ⟩ ≃ ⟨ El c ⟩)
    → SquareP (λ i j → B (compᵁ e f i j)) (link* e) (link* (e ∙ₑ f)) (refl′ (code* a)) (link* f)
  comp* e f = isSet→SquareP (λ i j → is-set-B (compᵁ e f i j)) _ _ _ _

elimProp : ∀ {ℓP} {P : Subᵁ → Type ℓP}
  → (∀ X → isProp (P X))
  → (code* : (a : ⟨ U ⟩) → P (codeᵁ a))
  → (X : Subᵁ) → P X
elimProp {P} is-prop-P code* = elimSet (isProp→isSet ∘ is-prop-P) code* link* where
  link* : ∀ {a b} → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩) → PathP (λ i → P (linkᵁ e i)) (code* a) (code* b)
  link* e = isProp→PathP (λ i → is-prop-P (linkᵁ e i)) _ _

uaᵁ : ∀ {a b} → ⟨ El a ⟩ ≃ ⟨ El b ⟩ → El a ≡ El b
uaᵁ = hSet≡ ∘ ua

Elᵁ : Subᵁ → hSet ℓ
Elᵁ = rec isGroupoidHSet
  El
  uaᵁ
  λ e f → ΣSquareProp (λ X → isPropIsSet) $ uaCompEquivSquare e f

module Path where
  code* : (a b : ⟨ U ⟩) → hSet ℓ
  code* a b .fst = ⟨ El a ⟩ ≃ ⟨ El b ⟩
  code* a b .snd = isOfHLevel≃ 2 (str (El a)) (str (El b))

  link* : ∀ a {b₀ b₁}
    → ⟨ El b₀ ⟩ ≃ ⟨ El b₁ ⟩
    → code* a b₀ ≡ code* a b₁
  link* a e = hSet≡ $ cong (⟨ El a ⟩ ≃_) $ ua e

  comp* : ∀ a {b₀ b₁ b₂}
    → (e : ⟨ El b₀ ⟩ ≃ ⟨ El b₁ ⟩)
    → (f : ⟨ El b₁ ⟩ ≃ ⟨ El b₂ ⟩)
    → Square (link* a e) (link* a (e ∙ₑ f)) refl (link* a f)
  comp* a e f = ΣSquareProp (λ X → isPropIsSet) $ goal where
    goal : Square
      (λ j → ⟨ El a ⟩ ≃ ua e j)
      (λ j → ⟨ El a ⟩ ≃ ua (e ∙ₑ f) j)
      refl
      (λ i → ⟨ El a ⟩ ≃ ua f i)
    goal i j = ⟨ El a ⟩ ≃ uaCompEquivSquare e f i j

  Code : ⟨ U ⟩ → Subᵁ → hSet ℓ
  Code a = rec isGroupoidHSet (code* a) (link* a) (comp* a)

  isSetCode : ∀ a X → isSet ⟨ Code a X ⟩
  isSetCode a X = str (Code a X)

  refl* : ∀ a → ⟨ Code a (codeᵁ a) ⟩
  refl* a = idEquiv ⟨ El a ⟩

  -- Jᵁ : ∀ {ℓP} (a : ⟨ U ⟩) → (P : ∀ Y → ⟨ Code a Y ⟩ → hProp ℓP)
  --   → (d : ⟨ P (codeᵁ a) (refl* a) ⟩)
  --   → ∀ Y r → ⟨ P Y r ⟩
  -- Jᵁ a P d = elimProp {! !} {! !}

  encode : (a : ⟨ U ⟩) (X : Subᵁ) → codeᵁ a ≡ X → ⟨ Code a X ⟩
  encode a X p = subst (λ - → ⟨ Code a - ⟩) p $ refl* a

  encode-filler : (a : ⟨ U ⟩) (X : Subᵁ) (p : codeᵁ a ≡ X) → PathP (λ i → ⟨ Code a (p i) ⟩) (refl* a) (encode a X p)
  encode-filler a X p = subst-filler (λ - → ⟨ Code a - ⟩) p $ refl* a

  {-
  isEquivEncode : (a : ⟨ U ⟩) (X : Subᵁ) → isEquiv (encode a X)
  isEquivEncode a = elimProp (λ X → isPropIsEquiv _) goal where
    fiber-equiv : (b : ⟨ U ⟩) (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩) → fiber (encode a (codeᵁ b)) e ≃ {! !}
    fiber-equiv b e =
      Σ[ p ∈ codeᵁ a ≡ codeᵁ b ] encode a (codeᵁ b) p ≡ e ≃⟨ Σ-cong-equiv-snd (λ p → {!  !}) ⟩
      Σ[ p ∈ codeᵁ a ≡ codeᵁ b ] subst (⟨ El a ⟩ ≃_) (cong (⟨_⟩ ∘ Elᵁ) p) (idEquiv ⟨ El a ⟩) ≡ e ≃⟨ Σ-cong-equiv-snd (λ p → invEquiv (PathP≃Path (λ i → ⟨ El a ⟩ ≃ ⟨ Elᵁ (p i) ⟩) (idEquiv _) e)) ⟩
      Σ[ p ∈ codeᵁ a ≡ codeᵁ b ] PathP (λ i → ⟨ El a ⟩ ≃ ⟨ Elᵁ (p i) ⟩) (idEquiv ⟨ El a ⟩) e ≃⟨ ΣPathP≃PathPΣ ⟩
      Path (Σ[ X ∈ Subᵁ ] ⟨ El a ⟩ ≃ ⟨ Elᵁ X ⟩) (codeᵁ a , idEquiv ⟨ El a ⟩) (codeᵁ b , e) ≃⟨ {! !} ⟩
      {! !} ≃∎
      where
        -- TODO: Eliminate into paths of hSets
        bar : (X : Subᵁ) → (⟨ El a ⟩ ≃ ⟨ Elᵁ X ⟩) ≡ ⟨ Code a X ⟩
        bar = elim {! !} (λ b → refl) (λ e → {!equivPathP !}) {! !}

        foo : (p : codeᵁ a ≡ codeᵁ b) → subst (⟨ El a ⟩ ≃_) (cong (⟨_⟩ ∘ Elᵁ) p) (idEquiv ⟨ El a ⟩) ≡ encode a (codeᵁ b) p
        foo p =
          subst (⟨ El a ⟩ ≃_) (cong (⟨_⟩ ∘ Elᵁ) p) (idEquiv ⟨ El a ⟩) ≡⟨⟩
          subst (λ X → ⟨ El a ⟩ ≃ ⟨ Elᵁ X ⟩) p (idEquiv ⟨ El a ⟩) ≡[ i ]⟨ subst (λ X → bar X i) p (idEquiv ⟨ El a ⟩) ⟩
          subst (λ X → ⟨ Code a X ⟩) p (idEquiv ⟨ El a ⟩) ≡⟨⟩
          encode a (codeᵁ b) p ∎

    contr-fib : (b : ⟨ U ⟩) (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩) → isContr (fiber (encode _ _) e)
    contr-fib b e = {! !}

    goal : (b : ⟨ U ⟩) → isEquiv (encode a (codeᵁ b))
    goal b .equiv-proof = contr-fib b
  -}

  encode-refl : (a : ⟨ U ⟩) → encode a _ refl ≡ refl* a
  encode-refl a = substRefl {B = λ - → ⟨ Code a - ⟩} {x = codeᵁ a} (refl* a)

  decode* : (a b : ⟨ U ⟩) → ⟨ El a ⟩ ≃ ⟨ El b ⟩ → codeᵁ a ≡ codeᵁ b
  decode* a b = linkᵁ

  unlink* : ∀ a {b₀ b₁}
    → (e : ⟨ El b₀ ⟩ ≃ ⟨ El b₁ ⟩)
    → PathP (λ i → ⟨ Code a (linkᵁ e i) ⟩ → codeᵁ a ≡ linkᵁ e i) (decode* a b₀) (decode* a b₁)
  unlink* a {b₀} {b₁} e = funExtNonDep goal where
    module _ {e₀ : ⟨ El a ⟩ ≃ ⟨ El b₀ ⟩} {e₁ : ⟨ El a ⟩ ≃ ⟨ El b₁ ⟩} (p : PathP (λ i → ⟨ El a ⟩ ≃ ua e i) e₀ e₁) where
      p-fun : PathP (λ i → ⟨ El a ⟩ → ua e i) (equivFun e₀) (equivFun e₁)
      p-fun i = equivFun (p i)

      -- p-path : PathP (λ i → ⟨ El a ⟩ ≡ ua e i) (ua e₀) (ua e₁)
      -- p-path i j = ua (p i) j

      have : e₀ ∙ₑ e ≡ e₁
      have = equivEq $ funExt $ →ua⁻ p-fun

      need : linkᵁ (e₀ ∙ₑ e) ≡ linkᵁ e₁
      need = cong linkᵁ have

      -- TODO: Rewrite `need` as a square and directly compose with `compᵁ e₀ e`
      -- to obtain this.
      goal : Square (linkᵁ e₀) (linkᵁ e₁) refl (linkᵁ e)
      goal = subst (λ - → Square (linkᵁ e₀) - refl (linkᵁ e)) need (compᵁ e₀ e)

  decode : (a : ⟨ U ⟩) → (X : Subᵁ) → ⟨ Code a X ⟩ → codeᵁ a ≡ X
  decode a = elimSet (λ X → isSet→ (isGroupoidSubᵁ (codeᵁ a) X)) (decode* a) (unlink* a)

  decode-refl* : (a : ⟨ U ⟩) → decode a (codeᵁ a) (refl* a) ≡ refl
  decode-refl* = idᵁ

  decode∘encode-refl : (a : ⟨ U ⟩) → decode a (codeᵁ a) (encode a (codeᵁ a) refl) ≡ refl
  decode∘encode-refl a = cong (decode _ _) (encode-refl a) ∙ decode-refl* a

  decode∘encode : (a : ⟨ U ⟩) (X : Subᵁ) (p : codeᵁ a ≡ X) → decode a X (encode a X p) ≡ p
  decode∘encode a X = J (λ X (p : codeᵁ a ≡ X) → decode a X (encode a X p) ≡ p) (decode∘encode-refl a)

  encode∘decode : (a : ⟨ U ⟩) (X : Subᵁ) (r : ⟨ Code a X ⟩) → encode a X (decode a X r) ≡ r
  encode∘decode a = elimProp (λ X → isPropΠ λ r → str (Code a X) _ r) goal
    where module _ (b : ⟨ U ⟩) (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩) where
      goalP-fun : PathP (λ i → ⟨ El a ⟩ → ua e i) (id _) (equivFun e)
      goalP-fun = ua-gluePathExt e

      goalP : PathP (λ i → ⟨ Code a (decode a (codeᵁ b) e i) ⟩) (idEquiv ⟨ El a ⟩) e
      goalP = equivPathP $ goalP-fun

      goal : subst (λ - → ⟨ Code a - ⟩) (decode a (codeᵁ b) e) (refl* a) ≡ e
      goal = fromPathP {A = λ i → ⟨ Code a (decode a (codeᵁ b) e i) ⟩} goalP

  encodeIso : (a : ⟨ U ⟩) (X : Subᵁ) → Iso (codeᵁ a ≡ X) ⟨ Code a X ⟩
  encodeIso a X .Iso.fun = encode a X
  encodeIso a X .Iso.inv = decode a X
  encodeIso a X .Iso.sec = encode∘decode a X
  encodeIso a X .Iso.ret = decode∘encode a X

  encodeEquiv : (a : ⟨ U ⟩) (X : Subᵁ) → (codeᵁ a ≡ X) ≃ ⟨ Code a X ⟩
  encodeEquiv a X = isoToEquiv (encodeIso a X)

  encodeEquiv' : (a b : ⟨ U ⟩) → (codeᵁ a ≡ codeᵁ b) ≃ (⟨ El a ⟩ ≃ ⟨ El b ⟩)
  encodeEquiv' a b = encodeEquiv a (codeᵁ b)

  module _ (is-strict : isStrict) where
    open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
    open Strict is-strict using (isInjectiveEl)

    uncodeᵁ : Subᵁ → ⟨ U ⟩
    uncodeᵁ = elimSet (λ _ → str U) (id ⟨ U ⟩) $ isInjectiveEl _ _

    rep : Subᵁ → Subᵁ
    rep = codeᵁ ∘ uncodeᵁ

    repᵝ : (X : Subᵁ) → ∥ rep X ≡ X ∥₁
    repᵝ = elimProp (λ X → PT.isPropPropTrunc) λ a → PT.∣ refl ∣₁
    
    repᵝ-link : ∀ {a b} → (e : ⟨ El a ⟩ ≃ ⟨ El b ⟩) → cong rep (linkᵁ e) ≡ linkᵁ e
    repᵝ-link {a} {b} e i j = {!compᵁ !}

    repᵝ' : (X : Subᵁ) → rep X ≡ X
    repᵝ' = elimSet (λ X → isGroupoidSubᵁ _ X) (λ a → refl) λ e → flipSquare $ the (_ ≡ _) {! !}
    
    isStrict→isInjectiveCodeᵁ : ∀ {a b} → codeᵁ a ≡ codeᵁ b → a ≡ b
    isStrict→isInjectiveCodeᵁ {b} p = Strict.isInjectiveEl is-strict _ _ $ encode _ (codeᵁ b) p
