module GpdCont.IterativeSets where

open import GpdCont.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Base using (transpEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Functions.Embedding as Embedding
  using ()
  renaming (hasPropFibers to isEmbedding ; hasPropFibersIsProp to isPropIsEmbedding)
open import Cubical.Functions.FunExtEquiv

module _ where
  private
    variable
      ℓA ℓB ℓC : Level
      A : Type ℓA
      B : Type ℓB
      C : Type ℓC
      f : A → B
      g : B → C

  _↪_ : ∀ {ℓA ℓB} → (A : Type ℓA) → (B : Type ℓB) → Type _
  A ↪ B = Σ (A → B) isEmbedding

  Embedding : ∀ ℓA {ℓB} (B : Type ℓB) → Type _
  Embedding ℓA B = TypeWithStr ℓA (λ A → A ↪ B)

  isEmbedding→LeftCancellableExt : {f : A → B} → isEmbedding f
    → ∀ {ℓC} {C : Type ℓC}
    → (g h : C → A) → (∀ c → f (g c) ≡ f (h c)) → ∀ c → g c ≡ h c
  isEmbedding→LeftCancellableExt {f} emb-f {C} g h p c = ext where
    fib₁ : fiber f (f (g c))
    fib₁ = g c , refl

    fib₂ : fiber f (f (g c))
    fib₂ = h c , (sym $ p c)

    fib₁≡fib₂ : fib₁ ≡ fib₂
    fib₁≡fib₂ = emb-f (f ∘ g $ c) fib₁ fib₂

    ext : g c ≡ h c
    ext = cong fst fib₁≡fib₂

  isEmbedding→LeftCancellable : {f : A → B} → isEmbedding f
    → ∀ {ℓC} {C : Type ℓC}
    → (g h : C → A) → f ∘ g ≡ f ∘ h → g ≡ h
  isEmbedding→LeftCancellable {f} emb-f {C} g h p = funExt $ isEmbedding→LeftCancellableExt emb-f g h (funExtS⁻ p)

  isEmbedding-∘ : isEmbedding g → isEmbedding f → isEmbedding (g ∘ f)
  isEmbedding-∘ {g} {f} emb-g emb-f = goal where
    goal : ∀ z → isProp (fiber (g ∘ f) z)
    goal z (x₁ , gfx₁≡z) (x₂ , gfx₂≡z) = ΣPathP (cong fst step₂ , {!cong snd step₂ !}) where
      step₁ : Path (fiber g z) (f x₁ , gfx₁≡z) (f x₂ , gfx₂≡z)
      step₁ = emb-g _ (f x₁ , gfx₁≡z) (f x₂ , gfx₂≡z)

      fib₁ : fiber f (f x₂)
      fib₁ .fst = x₁
      fib₁ .snd = cong fst step₁

      fib₂ : fiber f (f x₂)
      fib₂ .fst = x₂
      fib₂ .snd = refl

      step₂ : Path (fiber f (f x₂)) fib₁ fib₂
      step₂ = emb-f _ fib₁ fib₂

      x₁≡x₂ : x₁ ≡ x₂
      x₁≡x₂ = {! !} -- isEmbedding→LeftCancellableExt emb-g 


  _∘↪_ : (B ↪ C) → (A ↪ B) → (A ↪ C)
  (g ∘↪ f) .fst = g .fst ∘ f .fst
  (g ∘↪ f) .snd = isEmbedding-∘ (g .snd) (f .snd)
    

  EmbeddingΣProp : ∀ {ℓA ℓB} {A : Type ℓA} → {B : A → Type ℓB} → (∀ a → isProp (B a)) → Σ A B ↪ A
  EmbeddingΣProp is-prop-B .fst = fst
  EmbeddingΣProp is-prop-B .snd = goal where
    goal : ∀ a → isProp (fiber fst a)
    goal a ((a₁ , b₁) , fib₁) ((a₂ , b₂) , fib₂) = ΣPathP λ where
      .fst → Σ≡Prop is-prop-B (fib₁ ∙∙ refl ∙∙ sym fib₂)
      .snd i j → doubleCompPath-filler fib₁ refl (sym fib₂) (~ j) i

private
  _↔_ : ∀ {ℓA ℓB} (A : Type ℓA) (B : Type ℓB) → Type _
  A ↔ B = (A → B) × (B → A)


module EmbeddingIP {ℓA ℓB} (B : Type  ℓB) (f* g* : Embedding ℓA B) where
  open Σ f* renaming (fst to Aᶠ ; snd to f↪)
  open Σ g* renaming (fst to Aᵍ ; snd to g↪)
  open Σ f↪ renaming (fst to f ; snd to emb-f)
  open Σ g↪ renaming (fst to g ; snd to emb-g)

  toPath : (∀ b → (fiber f b ↔ fiber g b)) → f* ≡ g*
  toPath e = ΣPathP ({! !} , ΣPathP ({! !} , {! !})) where
    Aᶠ≡Aᵍ : Aᶠ ≡ Aᵍ
    Aᶠ≡Aᵍ = {! !}

data V∞ (ℓ : Level) : Type (ℓ-suc ℓ) where
  sup∞ : (A : Type ℓ) → (B : A → V∞ ℓ) → V∞ ℓ


private
  variable
    ℓ : Level

desup∞ : V∞ ℓ → Σ[ A ∈ Type ℓ ] (A → V∞ ℓ)
desup∞ (sup∞ A B) .fst = A
desup∞ (sup∞ A B) .snd = B

El∞ : V∞ ℓ → Type ℓ
El∞ = fst ∘ desup∞

el∞ : (x : V∞ ℓ) → (El∞ x → V∞ ℓ)
el∞ = snd ∘ desup∞

V∞Path : ∀ {x y : V∞ ℓ}
  → (p : El∞ x ≡ El∞ y)
  → (q : PathP (λ i → p i → V∞ ℓ) (el∞ x) (el∞ y))
  → x ≡ y
V∞Path {x = sup∞ A f} {sup∞ B g} p q i = sup∞ (p i) (q i)

_∈∞_ : (x y : V∞ ℓ) → Type _
x ∈∞ y = fiber (el∞ y) x

isIterativeSet : V∞ ℓ → Type (ℓ-suc ℓ)
isIterativeSet (sup∞ A B) = isEmbedding B × (∀ a → isIterativeSet (B a))

isPropIsIterativeSet : ∀ (x : V∞ ℓ) → isProp (isIterativeSet x)
isPropIsIterativeSet (sup∞ A B) = isProp× isPropIsEmbedding (isPropΠ $ isPropIsIterativeSet ∘ B)

isIterativeSet→isEmbedding-el∞ : (x : V∞ ℓ) → isIterativeSet x → isEmbedding (el∞ x)
isIterativeSet→isEmbedding-el∞ (sup∞ A B) = fst

isIterativeSetUnfold : {x : V∞ ℓ} → isIterativeSet x → (K : El∞ x) → isIterativeSet (el∞ x K)
isIterativeSetUnfold {x = sup∞ _ _} is-it-x = is-it-x .snd

V⁰ : (ℓ : Level) → Type (ℓ-suc ℓ)
V⁰ ℓ = Σ[ x ∈ V∞ ℓ ] isIterativeSet x

V⁰↪V∞ : V⁰ ℓ ↪ V∞ ℓ
V⁰↪V∞ = EmbeddingΣProp isPropIsIterativeSet

V⁰→V∞ : V⁰ ℓ → V∞ ℓ
V⁰→V∞ = fst V⁰↪V∞

V⁰Path : ∀ {x y : V⁰ ℓ}
  → (x .fst ≡ y .fst)
  → x ≡ y
V⁰Path = Σ≡Prop isPropIsIterativeSet

El⁰ : (x : V⁰ ℓ) → Type ℓ
El⁰ = El∞ ∘ fst

sup⁰ : (A : Type ℓ) → (B : A ↪ V⁰ ℓ) → V⁰ ℓ
sup⁰ A B .fst = sup∞ A (V⁰→V∞ ∘ B .fst)
sup⁰ A B .snd .fst = isEmbedding-∘ (snd V⁰↪V∞) (B .snd)
sup⁰ A B .snd .snd = snd ∘ B .fst

el⁰∞ : (x : V⁰ ℓ) → El⁰ x → V∞ ℓ
el⁰∞ = el∞ ∘ fst

isEmbedding-el⁰∞ : (x : V⁰ ℓ) → isEmbedding (el⁰∞ x)
isEmbedding-el⁰∞ = uncurry isIterativeSet→isEmbedding-el∞

El⁰↪V∞ : (x : V⁰ ℓ) → El⁰ x ↪ V∞ ℓ
El⁰↪V∞ x .fst = el⁰∞ x
El⁰↪V∞ x .snd = isEmbedding-el⁰∞ x

el⁰ : (x : V⁰ ℓ) → El⁰ x → V⁰ ℓ
el⁰ (x , is-it-x) K .fst = el∞ x K
el⁰ (x , is-it-x) K .snd = isIterativeSetUnfold is-it-x K

El⁰↪V⁰ : (x : V⁰ ℓ) → El⁰ x ↪ V⁰ ℓ
El⁰↪V⁰ x .fst = el⁰ x
El⁰↪V⁰ x .snd = {! !}

desup⁰ : V⁰ ℓ → Embedding ℓ (V⁰ ℓ)
desup⁰ x .fst = El⁰ x
desup⁰ x .snd = El⁰↪V⁰ x

_∈⁰_ : (x y : V⁰ ℓ) → Type _
(x , _) ∈⁰ (y , _) = x ∈∞ y

isProp-∈⁰ : ∀ (x y : V⁰ ℓ) → isProp (x ∈⁰ y)
isProp-∈⁰ (x , _) (y , is-it-y) = isIterativeSet→isEmbedding-el∞ y is-it-y x

_≡⁰_ : (x y : V⁰ ℓ) → Type _
x ≡⁰ y = ∀ z → (z ∈⁰ x) ↔ (z ∈⁰ y)

opaque
  isProp-≡⁰ : (x y : V⁰ ℓ) → isProp (x ≡⁰ y)
  isProp-≡⁰ x y = isPropΠ λ z
    → isProp×
      (isProp→ (isProp-∈⁰ z y))
      (isProp→ (isProp-∈⁰ z x))

opaque
  SIP⁰ : (x y : V⁰ ℓ) → (x ≡ y) ≃ (x ≡⁰ y)
  SIP⁰ = {! !}

isProp-el⁰″ : (x y : V⁰ ℓ) → (p : El⁰ x ≡ El⁰ y) → PathP (λ i → p i → V∞ ℓ) (el⁰∞ x) (el⁰∞ y)
isProp-el⁰″ {ℓ} x y p = isProp→PathP {B = λ i → p i → V∞ ℓ} isProp-line (el⁰∞ x) (el⁰∞ y) where
  isProp-line : ∀ i → isProp (p i → V∞ ℓ)
  isProp-line i = {!transpEquiv (λ i → isProp (p i → V∞ ℓ)) i !}

isProp-el⁰′ : (x y : V⁰ ℓ) → (p : El⁰ x ≡ El⁰ y) → PathP (λ i → p i → V∞ ℓ) (el⁰∞ x) (el⁰∞ y)
isProp-el⁰′ {ℓ} (sup∞ A B , (emb-B , it-B)) (sup∞ C D , (emb-D , it-D)) p = {! !} where
  open import Cubical.Functions.Fibration using (Fibration)
  open Embedding using (_≃Fib_ ; FibrationIP ; module EmbeddingIdentityPrinciple)
  open EmbeddingIdentityPrinciple

  B-fib : Fibration _ _
  B-fib .fst = A
  B-fib .snd = B

  D-fib : Fibration _ _
  D-fib .fst = C
  D-fib .snd = D

  fiber-equiv : ∀ (y : V∞ ℓ) → fiber B y ≃ fiber D y
  fiber-equiv y = propBiimpl→Equiv (emb-B y) (emb-D y) ⇒ ⇐ where
    ⇒ : fiber B y → fiber D y
    ⇒ (a , B[a]≡y) = transport p a , V∞Path {! !} {! !} -- {!isProp-el⁰′ (B a , it-B a) (D (transport p a) , it-D (transport p a))  !}

    ⇐ : fiber D y → fiber B y
    ⇐ (c , D[a]≡y) = transport (sym p) c , {!B[a]≡y !}

  IP : (B-fib ≃Fib D-fib) ≃ (B-fib ≡ D-fib)
  IP = FibrationIP B-fib D-fib

  goal : PathP (λ i → p i → V∞ ℓ) B D
  goal = {!cong snd $ (equivFun IP) fiber-equiv !}
  

isProp-el⁰ : (x y : V⁰ ℓ) → (p : El⁰ x ≡ El⁰ y) → PathP (λ i → p i → V∞ ℓ) (el⁰∞ x) (el⁰∞ y)
isProp-el⁰ {ℓ} (sup∞ A B , itset₁) (sup∞ C D , itset₂) p = J Motive Motive-refl p B D (itset₁ .fst) (itset₂ .fst) (itset₁ .snd) (itset₂ .snd) where
  Motive : (C : Type ℓ) (p : A ≡ C) → Type _
  Motive C p = ∀ (B : A → V∞ ℓ) (D : C → V∞ ℓ)
    → isEmbedding B
    → isEmbedding D
    → (∀ a → isIterativeSet (B a))
    → (∀ a → isIterativeSet (D a))
    → PathP (λ i → p i → V∞ ℓ) B D

  Motive-refl : ∀ {A : Type ℓ} (B D : A → V∞ ℓ)
    → isEmbedding B
    → isEmbedding D
    → (∀ a → isIterativeSet (B a))
    → (∀ a → isIterativeSet (D a))
    → B ≡ D
  Motive-refl {A} B D emb-B emb-D it-B it-D = funExt λ { a → cong fst (invEq (IP′ a) {! !}) } where
    -- open import Cubical.Functions.Fibration using (Fibration)
    -- open Embedding using (_≃Fib_ ; FibrationIP)

    -- B-fib : Fibration _ _
    -- B-fib .fst = A
    -- B-fib .snd = B

    -- D-fib : Fibration _ _
    -- D-fib .fst = A
    -- D-fib .snd = D

    -- IP : (B-fib ≃Fib D-fib) ≃ (B-fib ≡ D-fib)
    -- IP = {! !}

    B′ : (a : A) → V⁰ ℓ
    B′ a = B a , it-B a

    D′ : (a : A) → V⁰ ℓ
    D′ a = D a , it-D a

    goal : ∀ a → B′ a ≡⁰ D′ a
    goal a z .fst z∈Ba .fst = {! !}
    goal a z .fst z∈Ba .snd = {! !}
    goal a z .snd = {! !}

    goal′ : ∀ a → B′ a ≡ D′ a
    goal′ a = V⁰Path (V∞Path {! !} {! !})

    IP′ : ∀ a → (B′ a ≡ D′ a) ≃ (B′ a ≡⁰ D′ a)
    IP′ a = SIP⁰ (B′ a) (D′ a)

-- T⁰ : (X : Type ℓ) → Type (ℓ-suc ℓ)
-- T⁰ {ℓ} X = Σ[ A ∈ Type ℓ ] A ↪ X

opaque
  isSetV⁰ : isSet (V⁰ ℓ)
  isSetV⁰ x y = isOfHLevelRespectEquiv 1 (invEquiv (SIP⁰ x y)) (isProp-≡⁰ x y)

  isSetEl⁰ : (x : V⁰ ℓ) → isSet (El⁰ x)
  isSetEl⁰ = {! !}

V⁰→hSet : V⁰ ℓ → hSet ℓ
V⁰→hSet x .fst = El⁰ x
V⁰→hSet x .snd = isSetEl⁰ x

isInjectiveEl⁰ : ∀ {x y : V⁰ ℓ} → El⁰ x ≡ El⁰ y → x ≡ y
isInjectiveEl⁰ {x = x , is-it-x} {y = y , is-it-y} p = V⁰Path (V∞Path p q) where
  q : PathP (λ i → p i → V∞ _) (el∞ x) (el∞ y)
  q = isProp→PathP {B = λ i → p i → V∞ _} {! !} {! !} {! !}
