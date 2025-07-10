module GpdCont.Embedding where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Properties
open import Cubical.Reflection.StrictEquiv
open import Cubical.Functions.Embedding public

private
  variable
    ℓ : Level
    A A′ B : Type ℓ
    f : A → B

private
  symEquiv : ∀ {a b : A} → (a ≡ b) ≃ (b ≡ a)
  symEquiv = strictEquiv sym sym

hasContrFiberOfImage→isEmbedding : ((x : A) → isContr (fiber f (f x))) → isEmbedding f
hasContrFiberOfImage→isEmbedding contr-fib-of-im = hasPropFibersOfImage→isEmbedding (isContr→isProp ∘ contr-fib-of-im)

isCancellable→isEmbedding : ((x y : A) → (x ≡ y) ≃ (f x ≡ f y)) → isEmbedding f
isCancellable→isEmbedding {f} cancel-equiv = hasContrFiberOfImage→isEmbedding contr-fib-of-im where
  singl-fiber-equiv : ∀ x → singl x ≃ fiber f (f x)
  singl-fiber-equiv x = Σ-cong-equiv-snd λ y → cancel-equiv x y ∙ₑ symEquiv

  contr-fib-of-im : ∀ x → isContr (fiber f (f x))
  contr-fib-of-im x = isOfHLevelRespectEquiv 0 (singl-fiber-equiv x) (isContrSingl x)

Σ-map-fst : ∀ {B′ : A′ → Type ℓ} (f : A → A′) → (Σ A (B′ ∘ f)) → (Σ A′ B′)
Σ-map-fst f (a , b′) = (f a , b′)

-- TODO: Move somewhere else
isOfHLevelFunMapFst : ∀ {B′ : A′ → Type ℓ} (n : HLevel) (f : A → A′) → isOfHLevelFun n f → isOfHLevelFun n (Σ-map-fst {B′ = B′} f)
isOfHLevelFunMapFst {A′} {A} {B′} n f is-of-hlevel-f (a′ , b′) = isOfHLevelRespectEquiv n (fiber-equiv a′ b′) (is-of-hlevel-f a′) where
  fiber-equiv : ∀ (a′ : A′) (b′ : B′ a′) → fiber f a′ ≃ fiber (Σ-map-fst f) (a′ , b′)
  fiber-equiv a′ b′ =
    fiber f a′ ≃⟨ invEquiv (Σ-contractSnd (λ _ → isContrSinglP _ _)) ⟩
    Σ[ (a , p) ∈ fiber f a′ ] singlP (λ i → B′ (p (~ i))) b′ ≃⟨ Σ-assoc-≃ ⟩
    Σ[ a ∈ A ] Σ[ p ∈ f a ≡ a′ ] singlP (λ i → B′ (p (~ i))) b′ ≃⟨ strictEquiv (λ { (a , p , b , q) → a , p , b , symP q }) (λ { (a , p , b , q) → a , p , b , symP q }) ⟩
    Σ[ a ∈ A ] Σ[ p ∈ f a ≡ a′ ] Σ[ b ∈ B′ (f a) ] PathP (λ i → B′ (p i)) b b′ ≃⟨ Σ-cong-equiv-snd (λ a → strictEquiv (λ { (p , b , q) → (b , p , q) }) (λ { (b , p , q) → (p , b , q) })) ⟩
    Σ[ a ∈ A ] Σ[ b ∈ B′ (f a) ] Σ[ p ∈ f a ≡ a′ ] PathP (λ i → B′ (p i)) b b′ ≃⟨ Σ-cong-equiv-snd (λ a → Σ-cong-equiv-snd λ b → ΣPathP≃PathPΣ) ⟩
    Σ[ a ∈ A ] Σ[ b ∈ B′ (f a) ] (f a , b) ≡ (a′ , b′) ≃⟨ invEquiv Σ-assoc-≃ ⟩
    Σ[ (a , b) ∈ Σ A (B′ ∘ f) ] (f a , b) ≡ (a′ , b′) ≃∎

Σ-embed-fst : ∀ {B′ : A′ → Type ℓ} (e : A ↪ A′) → (Σ A (B′ ∘ e .fst)) ↪ (Σ A′ B′)
Σ-embed-fst {A′} {A} {B′} (e , is-emb) .fst = Σ-map-fst e
Σ-embed-fst {A′} {A} {B′} (e , is-emb) .snd = hasPropFibers→isEmbedding (isOfHLevelFunMapFst 1 e $ isEmbedding→hasPropFibers is-emb)

Σ-map-snd : ∀ {ℓB ℓB′} {B : A → Type ℓB} {B′ : A → Type ℓB′}
  → (f : ∀ a → B a → B′ a) → (Σ A B) → (Σ A B′)
Σ-map-snd f (a , b) = (a , f a b)

isOfHLevelFunMapSnd : ∀ {ℓB ℓB′} {B : A → Type ℓB} {B′ : A → Type ℓB′}
  → (n : HLevel)
  → (f : ∀ a → B a → B′ a)
  → (∀ a → isOfHLevelFun n (f a))
  → isOfHLevelFun n (Σ-map-snd f)
isOfHLevelFunMapSnd {A} {B} {B′} n f is-of-hlevel-f (a₀ , b₀) = isOfHLevelRespectEquiv n fiber-equiv (is-of-hlevel-f a₀ b₀) where
  fiber-equiv : fiber (f a₀) b₀ ≃ fiber (Σ-map-snd f) (a₀ , b₀)
  fiber-equiv =
    Σ[ b ∈ B a₀ ] f a₀ b ≡ b₀ ≃⟨ invEquiv (Σ-contractFst (isContrSingl a₀)) ⟩
    Σ[ (a , p) ∈ singl a₀ ] Σ[ b ∈ B a ] (PathP (λ i → B′ (p (~ i))) (f a b) b₀)
      ≃⟨ strictEquiv (λ { ((a , p) , b , q) → (a , b , sym p , q) }) (λ { (a , b , p , q) → ((a , sym p) , b , q) }) ⟩
    Σ[ a ∈ A ] Σ[ b ∈ B a ] Σ[ p ∈ a ≡ a₀ ] (PathP (λ i → B′ (p i)) (f a b) b₀)
      ≃⟨ Σ-cong-equiv-snd (λ a → Σ-cong-equiv-snd λ b → ΣPathP≃PathPΣ) ⟩
    Σ[ a ∈ A ] Σ[ b ∈ B a ] (a , f a b) ≡ (a₀ , b₀) ≃⟨ invEquiv Σ-assoc-≃ ⟩
    Σ[ x ∈ Σ A B ] Σ-map-snd f x ≡ (a₀ , b₀) ≃∎

Σ-embed-snd : ∀ {ℓB ℓB′} {B : A → Type ℓB} {B′ : A → Type ℓB′}
  → (e : ∀ a → B a ↪ B′ a)
  → Σ A B ↪ Σ A B′
Σ-embed-snd e .fst = Σ-map-snd (fst ∘ e)
Σ-embed-snd e .snd = hasPropFibers→isEmbedding $
  isOfHLevelFunMapSnd 1 (fst ∘ e) (isEmbedding→hasPropFibers ∘ snd ∘ e)

Σ-embed : ∀ {ℓB ℓB′} {B : A → Type ℓB} {B′ : A′ → Type ℓB′}
  → (e : A ↪ A′)
  → (f : ∀ a → B a ↪ B′ (e .fst a))
  → Σ A B ↪ Σ A′ B′
Σ-embed e f = compEmbedding (Σ-embed-fst e) (Σ-embed-snd f)
