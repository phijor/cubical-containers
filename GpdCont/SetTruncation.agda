module GpdCont.SetTruncation where

open import GpdCont.Prelude
open import GpdCont.Prelude.Square
open import GpdCont.Prelude.Notation
open import GpdCont.Equiv using (symEquiv)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (compr≡Equiv)
open import Cubical.Foundations.GroupoidLaws using (rCancel)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path as Path using (PathP≡compPath ; pathFiber)
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂) public
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.Fibration

private
  variable
    ℓA ℓB : Level
    A : Type ℓA
    B : A → Type ℓB

instance
  setTruncDo : Do ∥_∥₂
  setTruncDo .Do._>>=_ x f = ST.rec ST.isSetSetTrunc f x
  setTruncDo .Do.pure = ST.∣_∣₂

setTruncMapComp : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
  → (f :  A → B) (g : B → C)
  → ST.map g ∘ ST.map f ≡ ST.map (g ∘ f)
setTruncMapComp f g = funExt (ST.elim (λ _ → ST.isSetPathImplicit) λ _ → refl)

setTruncMapId : ST.map (id A) ≡ id ∥ A ∥₂
setTruncMapId = funExt $ ST.elim (λ x → ST.isSetPathImplicit) λ a → refl

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

setTruncateSndΣ≃ : ∥ Σ A B ∥₂ ≃ ∥ (Σ A (∥_∥₂ ∘ B)) ∥₂
setTruncateSndΣ≃ = isoToEquiv ST.IsoSetTruncateSndΣ

setTruncate⊎≃ : ∀ {B : Type ℓB} → ∥ A ⊎ B ∥₂ ≃ ∥ A ∥₂ ⊎ ∥ B ∥₂
setTruncate⊎≃ {A} {B} = isoToEquiv trunc-iso where
  is-set-sum : isSet (∥ A ∥₂ ⊎ ∥ B ∥₂)
  is-set-sum = isOfHLevel⊎ 0 ST.isSetSetTrunc ST.isSetSetTrunc

  trunc-iso : Iso _ _
  trunc-iso .Iso.fun = ST.rec is-set-sum (Sum.map ∣_∣₂ ∣_∣₂)
  trunc-iso .Iso.inv = Sum.rec (ST.map inl) (ST.map inr)
  trunc-iso .Iso.rightInv = Sum.elim
    (ST.elim (λ _ → isOfHLevelPath 2 is-set-sum _ _) λ _ → refl)
    (ST.elim (λ _ → isOfHLevelPath 2 is-set-sum _ _) λ _ → refl)
  trunc-iso .Iso.leftInv = ST.elim (λ _ → ST.isSetPathImplicit) $
    Sum.elim (λ _ → refl) (λ _ → refl)

setTruncEquiv : ∀ {B : Type ℓB} → A ≃ B → ∥ A ∥₂ ≃ ∥ B ∥₂
setTruncEquiv = isoToEquiv ∘ ST.setTruncIso ∘ equivToIso

squash-cong : ∀ {a a' : A} (p q : a ≡ a') → Square {A = ∥ A ∥₂} (cong ∣_∣₂ p) (cong ∣_∣₂ q) refl refl
squash-cong {a} {a'} p q = ST.squash₂ ∣ a ∣₂ ∣ a' ∣₂ (cong ∣_∣₂ p) (cong ∣_∣₂ q)

module elim→Gpd {B : ∥ A ∥₂ → Type ℓB}
  (is-groupoid-B : ∀ a → isGroupoid (B a))
  (f : ∀ a → B ∣ a ∣₂)
  (cong-f-const : ∀ a a' (p q : a ≡ a') → SquareP (λ i j → B (squash-cong p q i j)) (cong f p) (cong f q) refl refl)
  where
  fun-Σ : ∥ A ∥₂ → Σ[ x ∈ ∥ A ∥₂ ] B x
  fun-Σ = ST.rec→Gpd.fun (isGroupoidΣ (isSet→isGroupoid ST.isSetSetTrunc) is-groupoid-B) [-]* const-square
    where
      [-]* : A → Σ[ x ∈ ∥ A ∥₂ ] B x
      [-]* a .fst = ∣ a ∣₂
      [-]* a .snd = f a

      module _ (a a' : A) (p q : a ≡ a') where
        const-square : Square (cong [-]* p) (cong [-]* q) refl refl
        const-square = ΣSquare (squash-cong p q , cong-f-const a a' p q)

  rep : ∥ A ∥₂ → ∥ A ∥₂
  rep = fst ∘ fun-Σ

  repᵝ : (x : ∥ A ∥₂) → (rep x) ≡ x
  repᵝ = ST.elim (λ x → ST.isSetPathImplicit) λ a → refl′ ∣ a ∣₂

  fun' : (x : ∥ A ∥₂) → B (rep x)
  fun' = snd ∘ fun-Σ

  fun : (x : ∥ A ∥₂) → B x
  fun x = subst B (repᵝ x) (fun' x)

  fun-filler : (x : ∥ A ∥₂) → PathP (λ i → B (repᵝ x i)) (fun' x) (fun x)
  fun-filler x = subst-filler B (repᵝ x) (snd (fun-Σ x))

  funᵝ : (a : A) → fun ∣ a ∣₂ ≡ f a
  funᵝ a = transportRefl (fun' ∣ a ∣₂)

open elim→Gpd
  using ()
  renaming (fun to elim→Gpd ; funᵝ to elim→Gpdᵝ)
  public

PathSetTrunc≃PropTruncPath : {a b : A} → (∣ a ∣₂ ≡ ∣ b ∣₂) ≃ ∥ a ≡ b ∥₁
PathSetTrunc≃PropTruncPath = isoToEquiv ST.PathIdTrunc₀Iso

merePath→pathSetTrunc : {a b : A} → ∥ a ≡ b ∥₁ → ∣ a ∣₂ ≡ ∣ b ∣₂
merePath→pathSetTrunc = Iso.inv ST.PathIdTrunc₀Iso

pathSetTrunc→merePath : {a b : A} → ∣ a ∣₂ ≡ ∣ b ∣₂ → ∥ a ≡ b ∥₁
pathSetTrunc→merePath = Iso.fun ST.PathIdTrunc₀Iso

pathSetTrunc→recProp : ∀ {ℓP} {P : Type ℓP} → isProp P
  → {a b : A} → (f : a ≡ b → P)
  → ∣ a ∣₂ ≡ ∣ b ∣₂ → P
pathSetTrunc→recProp {P} is-prop-P f p = PT.rec is-prop-P f (pathSetTrunc→merePath p)

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
