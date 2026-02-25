module GpdCont.GroupoidQuotients where

open import GpdCont.Prelude
open import GpdCont.Prelude.Square
open import GpdCont.Equiv
open import GpdCont.HomotopySet
open import GpdCont.Univalence

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (congPathEquiv)
open import Cubical.Foundations.GroupoidLaws using (compPathRefl)
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.GroupoidQuotients as GQ using (_//_ ; [_])

open BinaryRelation using (isTrans ; impliesIdentity ; isEquivRel)

module Test {ℓA ℓR} {A : Type ℓA} (R : A → A → Type ℓR) where
  apᴿ : (a b : A) → a ≡ b → (∀ z → R z a ≡ R z b)
  apᴿ a b p z = cong (R z) p

  apᴾ : {a b : A} → (p : a ≡ b) → PathP (λ i → {! !}) {! !} {! !} → {! !}
  apᴾ = {! !}

  record isExtensionalᴾ : Type (ℓ-max ℓA (ℓ-suc ℓR)) where
    field
      extensional : (a b : A) → isContr ((∀ z → R z a ≃ R z b) ≃ R a b)

  record isExtensional' : Type (ℓ-max ℓA (ℓ-suc ℓR)) where
    field
      extensional : (a b : A) → isEquiv (apᴿ a b)

    ext-equiv : ∀ a b → (a ≡ b) ≃ (∀ z → R z a ≡ R z b)
    ext-equiv a b .fst = apᴿ a b
    ext-equiv a b .snd = extensional a b

    ext : ∀ {a b} → (∀ z → R z a ≡ R z b) → a ≡ b
    ext {a} {b} = invEq (ext-equiv a b)

    ext⁻ : ∀ {a b} → a ≡ b → (∀ z → R z a ≡ R z b)
    ext⁻ {a} {b} = apᴿ a b

    extP : ∀ {a b} (r : R a b) → PathP (λ i → R a {!ext  !}) {! !} {! !}
    extP = {! !}

module Universe {ℓ} (U : hSet ℓ) (El : ⟨ U ⟩ → hSet ℓ) (injEl : ∀ a b → ⟨ El a ⟩ ≃ ⟨ El b ⟩ → a ≡ b) where
  _≃ᵁ_ : (a b : ⟨ U ⟩) → Type ℓ
  a ≃ᵁ b = ⟨ El a ⟩ ≃ ⟨ El b ⟩

  propit : (a b : ⟨ U ⟩) → isProp (∀ z → (z ≃ᵁ a) ≡ (z ≃ᵁ b))
  propit a b = isPropΠ λ z p q i j → {! !}

  ext : ∀ {a b} → (∀ z → (⟨ El z ⟩ ≃ ⟨ El a ⟩) ≡ (⟨ El z ⟩ ≃ ⟨ El b ⟩)) → a ≡ b
  ext {a} {b} mk-ext = injEl _ _ $ transport (mk-ext a) $ idEquiv _

  foo : ∀ a b (e : ∀ z → (⟨ El z ⟩ ≃ ⟨ El a ⟩) ≡ (⟨ El z ⟩ ≃ ⟨ El b ⟩)) → Test.apᴿ _≃ᵁ_ _ _ (ext e) ≡ e
  foo a b e = funExt λ z → the (cong (z ≃ᵁ_) (ext e) ≡ e z) λ i j → {! ⟨ El z ⟩ ≃_   !}

  is-ext : Test.isExtensional' _≃ᵁ_
  is-ext .Test.isExtensional'.extensional = {! !}

record isExtensional {ℓA ℓR} {A : Type ℓA} (R : A → A → Type ℓR) : Type (ℓ-max ℓA (ℓ-suc ℓR)) where
  field
    extensional : (a b : A) → (∀ z → R z a ≡ R z b) ≃ R a b

  extensional⁻ : (a b : A) → R a b ≃ (∀ z → R z a ≡ R z b)
  extensional⁻ a b = invEquiv (extensional a b)

  extensional' : (a b : A) → (flip R a ≡ flip R b) ≃ R a b
  extensional' = {! !}

  ext : ∀ {a b} → (∀ z → R z a ≡ R z b) → R a b
  ext {a} {b} = equivFun (extensional a b)

  ext⁻ : ∀ {a b} → R a b → (∀ z → R z a ≡ R z b)
  ext⁻ = invEq (extensional _ _)

  is-emb-ext : ∀ a b → isEmbedding (ext {a} {b})
  is-emb-ext a b = isEquiv→isEmbedding (equivIsEquiv (extensional a b))

  is-emb-ext⁻ : ∀ a b → isEmbedding (ext⁻ {a} {b})
  is-emb-ext⁻ a b = isEquiv→isEmbedding (equivIsEquiv $ invEquiv (extensional a b))

  id≃ : ∀ a → R a a ≃ {! !}
  id≃ a =
    R a a ≃⟨ {! !} ⟩
    (∀ z → R z a ≡ R z a) ≃⟨ {! !} ⟩
    {! !} ≃∎

  inv≃ : ∀ a b → R a b ≃ R b a
  inv≃ a b = (extensional⁻ a b) ∙ₑ (equivΠCod λ z → symEquiv) ∙ₑ (extensional b a)

  ∙≃ : ∀ a b c → (R a b × R b c) ≃ R a c
  ∙≃ a b c =
    (R a b × R b c) ≃⟨ ≃-× (extensional⁻ a b) (extensional⁻ b c) ⟩
    ((∀ z → R z a ≡ R z b) × (∀ z → R z b ≡ R z c)) ≃⟨ invEquiv Σ-Π-≃ ⟩
    (∀ z → (R z a ≡ R z b) × (R z b ≡ R z c)) ≃⟨ equivΠCod (λ z → {! !}) ⟩
    (∀ z → R z a ≡ R z c) ≃⟨ extensional a c ⟩
    R a c ≃∎

  ∙≃' : ∀ a c → (∀ b → R a b × R b c) ≃ R a c
  ∙≃' a c =
    (∀ b → R a b × R b c) ≃⟨ equivΠCod (λ b → ≃-× (extensional⁻ a b) (extensional⁻ b c)) ⟩
    (∀ b → ((∀ z → R z a ≡ R z b) × (∀ z → R z b ≡ R z c))) ≃⟨ equivΠCod (λ b → invEquiv Σ-Π-≃) ⟩
    (∀ b z → (R z a ≡ R z b) × (R z b ≡ R z c)) ≃⟨ {! !} ⟩
    (∀ z → R z a ≡ R z c) ≃⟨ extensional a c ⟩
    R a c ≃∎

  is-equiv-rel : isEquivRel R
  is-equiv-rel .isEquivRel.reflexive a = ext λ z → refl′ $ R z a
  is-equiv-rel .isEquivRel.symmetric a b = equivFun (inv≃ a b)
  is-equiv-rel .isEquivRel.transitive a b c aRb bRc = ext λ z → ext⁻ aRb z ∙ ext⁻ bRc z

  open isEquivRel is-equiv-rel public

  unwrap : ∀ {a b} {r s : ∀ z → R z a ≡ R z b}
    → (ext⁻ (ext r)) ≡ (ext⁻ (ext s))
    → r ≡ s
  unwrap {r} {s} p = sym (retEq (extensional _ _) r) ∙∙ p ∙∙ (retEq (extensional _ _) s)

  wrap : ∀ {a b} {r s : ∀ z → R z a ≡ R z b}
    → r ≡ s
    → (ext⁻ (ext r)) ≡ (ext⁻ (ext s))
  wrap {r} {s} = cong (ext⁻ ∘ ext)

  ext⁻→≡ᴿ : ∀ {a b} {r s : R a b}
    → ext⁻ r ≡ ext⁻ s
    → r ≡ s
  ext⁻→≡ᴿ {a} {b} {r} {s} = isEmbedding→Inj (is-emb-ext⁻ a b) r s

  ext≡ : ∀ {a b} {r s : ∀ z → R z a ≡ R z b}
    → (∀ z → r z ≡ s z)
    → ext r ≡ ext s
  ext≡ {a} {b} {r} {s} h = cong ext $ funExt h

  idᴿ : ∀ a → R a a
  idᴿ = reflexive

  _∙ᴿ_ : ∀ {a b c} → R a b → R b c → R a c
  _∙ᴿ_ {a} {b} {c} = transitive a b c

  invᴿ : ∀ {a b} → R a b → R b a
  invᴿ {a} {b} = symmetric a b

  assocᴿ : ∀ {a b c d} (r : R a b) (s : R b c) (t : R c d)
     → (r ∙ᴿ s) ∙ᴿ t ≡ r ∙ᴿ (s ∙ᴿ t)
  assocᴿ r s t = ext≡ λ z →
    ext⁻ (r ∙ᴿ s) z ∙ ext⁻ t z ≡[ i ]⟨ retEq (extensional _ _) (λ z → ext⁻ r z ∙ ext⁻ s z) i z ∙ ext⁻ t z ⟩
    (ext⁻ r z ∙ ext⁻ s z) ∙ ext⁻ t z ≡⟨ {! !} ⟩
    ext⁻ r z ∙ ext⁻ (s ∙ᴿ t) z ∎

  ext⁻-idᴿ : ∀ a → ext⁻ (idᴿ a) ≡ λ z → refl′ (R z a)
  ext⁻-idᴿ a = retEq (extensional _ _) _

  ext-comp-square' : ∀ {a b c}
    → (r : R a b) (s : R b c)
    → ∀ z → Square (ext⁻ r z) (ext⁻ r z ∙ ext⁻ s z) refl (ext⁻ s z)
  ext-comp-square' r s z = pathComp→compSquareFiller (ext⁻ r z) (ext⁻ s z)

  ext-comp-square : ∀ {a b c}
    → (r : R a b) (s : R b c)
    → ∀ z → Square (ext⁻ r z) (ext⁻ (r ∙ᴿ s) z) refl (ext⁻ s z)
  ext-comp-square r s z = subst (λ - → Square (ext⁻ r z) - refl (ext⁻ s z)) goal $ ext-comp-square' r s z
    where
      goal' : (λ z → ext⁻ r z ∙ ext⁻ s z) ≡ ext⁻ (ext λ z → ext⁻ r z ∙ ext⁻ s z)
      goal' = sym (retEq (extensional _ _) (λ z → ext⁻ r z ∙ ext⁻ s z))

      goal : (ext⁻ r z ∙ ext⁻ s z) ≡ ext⁻ (ext λ z → ext⁻ r z ∙ ext⁻ s z) z
      goal = goal' ≡$ z

  ext⁻-comp : ∀ {a b c} → (r : R a b) (s : R b c)
    → ext⁻ (r ∙ᴿ s) ≡ (λ z → ext⁻ r z ∙ ext⁻ s z)
  ext⁻-comp r s = funExt λ z → sym $ compSquareFillerUnique $ ext-comp-square r s z

  comp-id-idᴿ : ∀ a → idᴿ a ∙ᴿ idᴿ a ≡ idᴿ a
  comp-id-idᴿ a = cong ext $ funExt λ z → (cong (λ p → p ∙ p) (ext⁻-idᴿ a ≡$ z)) ∙ sym compPathRefl

  comp-id-rightᴿ : ∀ {a b} → (r : R a b) → idᴿ a ∙ᴿ r ≡ r
  comp-id-rightᴿ = {! !}

private
  -- Sanity check: extensionality does not imply identity (otherwise any type would be contractible)
  is-extensional-total : ∀ {ℓ} {A : Type ℓ} → isExtensional (λ (a b : A) → Unit)
  is-extensional-total .isExtensional.extensional a b = isContr→≃Unit (isContrΠ λ z → isOfHLevel≡ 0 isContrUnit isContrUnit)

module _ {ℓA ℓR} {A : Type ℓA}
  (R : A → A → Type ℓR)
  (is-set-R : ∀ a b → isSet (R a b))
  (is-ext : isExtensional R)
  -- (is-trans-R : isTrans R)
  -- (implies-id : impliesIdentity R)
  -- (pres∙ : ∀ {a b c} → (r : R a b) (s : R b c) → Square (implies-id r) (implies-id $ is-trans-R _ _ _ r s) refl (implies-id s))
  where
  private
    open module R = isExtensional is-ext

    A//R = A // R.transitive

    module A//R where
      private
        variable ℓ : Level

      eq// : {a b : A} → R a b → [ a ] ≡ [ b ]
      eq// = GQ.eq// {Rt = R.transitive}

      rec : {B : Type ℓ}
        → isGroupoid B
        → (f : A → B)
        → (feq : {a b : A} (r : R a b) → f a ≡ f b)
        → ({a b c : A} (r : R a b) (s : R b c)
              → Square (feq r) (feq (r ∙ᴿ s)) refl (feq s))
        → (x : A//R)
        → B
      rec = GQ.rec R.transitive

      elimSet : {B : A//R → Type ℓ}
        → ((x : A//R) → isSet (B x))
        → (f : (a : A) → B [ a ])
        → ({a b : A} (r : R a b) → PathP (λ i → B (eq// r i)) (f a) (f b))
        → (x : A//R)
        → B x
      elimSet = GQ.elimSet R.transitive

      refl// : (a : A) → eq// (R.idᴿ a) ≡ refl
      refl// a = λ i j → hcomp {φ = ∂ i ∨ ∂ j} (sides i j) (base i j) where
        sides : (i j k : I) → Partial (∂ i ∨ ∂ j) A//R
        sides i j k (i = i0) = GQ.comp// (idᴿ a) (idᴿ a) (~ k) j
        sides i j k (i = i1) = GQ.eq// (idᴿ a) (j ∧ ~ k)
        sides i j k (j = i0) = [ a ]
        sides i j k (j = i1) = GQ.eq// (idᴿ a) (~ k)

        base : eq// (R.idᴿ a ∙ᴿ R.idᴿ a) ≡ eq// (R.idᴿ a)
        base = cong eq// $ comp-id-idᴿ a

  module _ (a : A) where
    Code* : (b : A) → hSet _
    Code* b .fst = R a b
    Code* b .snd = is-set-R a b

    Link* : ∀ {b₀ b₁ : A}
      → R b₀ b₁
      → Code* b₀ ≡ Code* b₁
    Link* {b₀} {b₁} r = hSet≡ $ ext⁻ r a

    Comp* : ∀ {b₀ b₁ b₂}
      → (r : R b₀ b₁)
      → (s : R b₁ b₂)
      → Square (Link* r) (Link* $ (r ∙ᴿ s)) refl (Link* s)
    Comp* r s = ΣSquareProp (λ X → isPropIsSet) (ext-comp-square r s a)

    Code : A//R → hSet _
    Code = A//R.rec isGroupoidHSet Code* Link* Comp*

    refl* : ⟨ Code [ a ] ⟩
    refl* = idᴿ a

    encode : (x : A//R) → [ a ] ≡ x → ⟨ Code x ⟩
    encode x p = subst (λ - → ⟨ Code - ⟩) p refl*

    encode-refl : encode [ a ] refl ≡ refl*
    encode-refl = substRefl {B = λ - → ⟨ Code - ⟩} {x = [ a ]} refl*

    decode* : (b : A) → R a b → Path A//R [ a ] [ b ]
    decode* b = GQ.eq// {a = a} {b = b}

    decode-comp' : (b₀ b₁ : A) (r : R b₀ b₁)
      → PathP (λ i → ext⁻ r a i → Path A//R [ a ] (GQ.eq// r i)) (decode* b₀) (decode* b₁)
    decode-comp' b₀ b₁ r = {! !}

    decode-comp : (b₀ b₁ : A) (r : R b₀ b₁)
      → PathP (λ i → ⟨ Code (GQ.eq// r i) ⟩ → Path A//R [ a ] (GQ.eq// r i)) (decode* b₀) (decode* b₁)
    decode-comp b₀ b₁ r = funExtNonDep goal where
      module _ {r₀ : R a b₀} {r₁ : R a b₁} (p : PathP (λ i → ext⁻ r a i) r₀ r₁) where

        test : PathP (λ i → ext⁻ r a i) r₀ r₁ ≃ ((r₀ ∙ᴿ r) ≡ transport (λ i → ext⁻ r a i) r₀)
        test = congPathEquiv {A = λ i → ext⁻ r a i} {B = λ i → R a b₁} $
          lineEquiv {! !} {! !} {! !}
          where
            f : (i : I) → ext⁻ r a i → R a b₁
            f i = {! coei→1 (λ i → p i) !}

        foo : Square {! !} {! !} {! ext⁻ r₀ a !} {! !}
        foo i = {! (p i)  !}

        help : (r₀ ∙ᴿ r) ≡ transport (λ i → ext⁻ r a i) r₀
        help =
          ext (λ z → ext⁻ r₀ z ∙ ext⁻ r z) ≡⟨ {! !} ⟩
          transport (λ i → ext⁻ r a i) r₀ ∎

        sq : ∀ z → Square (ext⁻ r₀ z) (ext⁻ r₁ z) refl (ext⁻ r z)
        sq z i j = {!  fromPathP p  !}

        lemma' : (λ z → (ext⁻ r₀ z) ∙ (ext⁻ r z)) ≡ ext⁻ r₁
        lemma' = {! !}

        lemma : ∀ z → (ext⁻ r₀ z) ∙ (ext⁻ r z) ≡ ext⁻ r₁ z
        lemma z = compSquareFillerUnique $ sq z

        have : (r₀ ∙ᴿ r) ≡ r₁
        have =
          ext (λ z → (ext⁻ r₀ z) ∙ (ext⁻ r z)) ≡[ i ]⟨ ext (λ z → lemma z i) ⟩
          ext (λ z → (ext⁻ r₁ z)) ≡⟨ secEq (extensional _ _) r₁ ⟩
          r₁ ∎

        need : (GQ.eq// (r₀ ∙ᴿ r)) ≡ (GQ.eq// r₁)
        need = cong GQ.eq// have

        goal : Square (GQ.eq// r₀) (GQ.eq// r₁) refl (GQ.eq// r)
        goal = λ i j → hcomp {φ = ∂ i ∨ ∂ j} (sides i j) (base i j) where
          sides : (i j k : I) → Partial (∂ i ∨ ∂ j) A//R
          sides i j k (i = i0) = GQ.eq// r₀ j
          sides i j k (i = i1) = need k j
          sides i j k (j = i0) = [ a ]
          sides i j k (j = i1) = GQ.eq// r i

          base : Square (GQ.eq// r₀) (GQ.eq// (r₀ ∙ᴿ r)) refl (GQ.eq// r)
          base = GQ.comp// r₀ r

    decode : (x : A//R) → ⟨ Code x ⟩ → [ a ] ≡ x
    decode = A//R.elimSet (λ x → isSet→ (GQ.squash// [ a ] x))
      decode*
      (decode-comp _ _)

    decode-refl : decode [ a ] refl* ≡ refl
    decode-refl = A//R.refl// a
