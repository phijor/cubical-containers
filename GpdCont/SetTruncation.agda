module GpdCont.SetTruncation where

open import GpdCont.Prelude
open import GpdCont.Equiv using (symEquiv)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (compr≡Equiv)
open import Cubical.Foundations.GroupoidLaws using (rCancel)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path as Path using (PathP≡compPath ; pathFiber)
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.Fibration

private
  variable
    ℓA ℓB : Level
    A : Type ℓA
    B : A → Type ℓB

IsoSetTruncateFstΣ : isSet A → Iso ∥ Σ A B ∥₂ (Σ A (∥_∥₂ ∘ B))
IsoSetTruncateFstΣ {A} {B} is-set-A = go where
  isSetΣA∥B∥ : isSet (Σ A (∥_∥₂ ∘ B))
  isSetΣA∥B∥ = isSetΣ is-set-A λ a → ST.isSetSetTrunc
  go : Iso _ _
  go .Iso.fun = ST.rec isSetΣA∥B∥ λ { (a , b) → a , ST.∣ b ∣₂ }
  go .Iso.inv = uncurry λ a → ST.rec ST.isSetSetTrunc λ { b → ST.∣ a , b ∣₂ }
  go .Iso.rightInv = uncurry λ a → ST.elim (λ ∣b∣ → isProp→isSet (isSetΣA∥B∥ _ (a , ∣b∣))) λ _ → refl
  go .Iso.leftInv = ST.elim (λ ∣a,b∣ → isProp→isSet (ST.isSetSetTrunc _ ∣a,b∣)) λ _ → refl

setTruncateFstΣ≃ : isSet A → ∥ Σ A B ∥₂ ≃ (Σ A (∥_∥₂ ∘ B))
setTruncateFstΣ≃ = isoToEquiv ∘ IsoSetTruncateFstΣ

setTruncEquiv : ∀ {B : Type ℓB} → A ≃ B → ∥ A ∥₂ ≃ ∥ B ∥₂
setTruncEquiv = isoToEquiv ∘ ST.setTruncIso ∘ equivToIso

PathSetTrunc≃PropTruncPath : {a b : A} → (∣ a ∣₂ ≡ ∣ b ∣₂) ≃ ∥ a ≡ b ∥₁
PathSetTrunc≃PropTruncPath = isoToEquiv ST.PathIdTrunc₀Iso

componentEquiv : (A : Type ℓA) → A ≃ (Σ[ x ∈ ∥ A ∥₂ ] fiber ∣_∣₂ x)
componentEquiv A = totalEquiv {B = ∥ A ∥₂} {E = A} ∣_∣₂

isSurjection-∣-∣₂ : ∀ (A : Type ℓA) → isSurjection (∣_∣₂ {A = A})
isSurjection-∣-∣₂ A = (ST.elim (λ _ → isProp→isSet PT.isPropPropTrunc) λ { a → PT.∣ a , refl ∣₁ })

isConnected-fiber-∣-∣₂ : ∀ (x : ∥ A ∥₂) → isContr ∥ fiber ∣_∣₂ x ∥₂
isConnected-fiber-∣-∣₂ {A} = ST.elim (λ x → isProp→isSet isPropIsContr) contr where
  lemma : ∀ {a b : A} → (p : ∣ b ∣₂ ≡ ∣ a ∣₂) → ∣ a , refl {x = ∣ a ∣₂} ∣₂ ≡ ∣ b , p ∣₂
  lemma {a} {b} p = PT.elim {P = λ p' → ∣ a , refl ∣₂ ≡ ∣ b , p ∣₂} (λ _ → ST.squash₂ _ _)
    (λ p' → cong ∣_∣₂ (ΣPathP (sym p' , isProp→PathP (λ i → ST.squash₂ ∣ p' (~ i) ∣₂ ∣ a ∣₂) (λ _ → ∣ a ∣₂) p)))
    (ST.PathIdTrunc₀Iso .Iso.fun p)

  contr : (a : A) → isContr ∥ fiber ∣_∣₂ ∣ a ∣₂ ∥₂
  contr a .fst = ∣ a , refl {x = ∣ a ∣₂} ∣₂
  contr a .snd = ST.elim (λ ∣fib∣ → ST.isSetPathImplicit) λ { (b , p) → lemma p }

isEmbeddingCong→hasSetFibers : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
  → (∀ (x y : A) → isEmbedding (cong {x = x} {y = y} f))
  → ∀ b → isSet (fiber f b)
isEmbeddingCong→hasSetFibers {A} {B} f emb = set-fibers where
  cong-f : ∀ x y → x ≡ y → f x ≡ f y
  cong-f _ _ = cong f

  fiber-equivᴰ : ∀ (b : B) (x y : A) → (p : f x ≡ b) → (r : x ≡ y) → (q : f y ≡ b)
    → PathP (λ i → f (r i) ≡ b) p q ≃ (cong f r ≡ p ∙ sym q)
  fiber-equivᴰ b x y p = J
    (λ y r → (q : f y ≡ b) → PathP (λ i → f (r i) ≡ b) p q ≃ (cong f r ≡ p ∙ sym q))
    λ q →
      PathP (λ i → f x ≡ b) p q           ≃⟨ pathToEquiv (Path.PathP≡Path (λ i → f x ≡ b) p q) ⟩
      (subst (λ x → f x ≡ b) refl p) ≡ q  ≃⟨ substEquiv (_≡ q) (substRefl {B = λ x → f x ≡ b} p) ⟩
      p ≡ q                               ≃⟨ symEquiv ⟩
      q ≡ p                               ≃⟨ compr≡Equiv q p (sym q) ⟩
      q ∙ sym q ≡ p ∙ sym q               ≃⟨ substEquiv (_≡ p ∙ sym q) (rCancel q) ⟩
      refl ≡ p ∙ sym q                    ≃∎

  fiber-equiv : ∀ (b : B) (x y : A) → (p : f x ≡ b) → (q : f y ≡ b)
    → Path (fiber f b) (x , p) (y , q) ≃ fiber (cong-f x y) (p ∙ sym q)
  fiber-equiv b x y p q =
    (x , p) ≡ (y , q) ≃⟨ invEquiv ΣPathP≃PathPΣ ⟩
    Σ[ r ∈ x ≡ y ] PathP (λ i → f (r i) ≡ b) p q ≃⟨ Σ-cong-equiv-snd (λ r → fiber-equivᴰ b x y p r q) ⟩
    Σ[ r ∈ x ≡ y ] cong f r ≡ p ∙ sym q ≃⟨⟩
    fiber (cong-f x y) (p ∙ sym q) ≃∎

  set-fibers : ∀ b → isSet (fiber f b)
  set-fibers b (x , p) (y , q) = isOfHLevelRespectEquiv 1
    (invEquiv $ fiber-equiv b x y p q)
    (isEmbedding→hasPropFibers (emb x y) (p ∙ sym q))
