module GpdCont.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path using (PathP≡compPath)
open import Cubical.Foundations.Univalence as UA hiding (ua ; ua→) public
open import Cubical.Foundations.Univalence using (ua-unglue ; unglueIsEquiv ; Glue)

private
  variable
    ℓ : Level
    A B C : Type ℓ

  ∂ : I → I
  ∂ i = i ∨ ~ i

ua : ∀ {ℓ} {A B : Type ℓ} → A ≃ B → A ≡ B
ua = UA.ua

ua-system : {A B : Type ℓ} (e : A ≃ B) → ∀ φ → Partial (∂ φ) (Σ[ T ∈ Type ℓ ] T ≃ B)
ua-system {A} {B} e φ = λ where
  (φ = i0) → A , e
  (φ = i1) → B , idEquiv B

ua-unglue-isEquiv : (e : A ≃ B) → ∀ φ → isEquiv (ua-unglue e φ)
ua-unglue-isEquiv {A} {B} e φ = unglueIsEquiv B (∂ φ) (ua-system e φ)

ua-unglue-equiv′ : (e : A ≃ B) → ∀ φ → ua e φ ≃ B
ua-unglue-equiv′ e φ .fst = ua-unglue e φ
ua-unglue-equiv′ e φ .snd = ua-unglue-isEquiv e φ

lineEquiv : {A B : I → Type ℓ} (f : (i : I) → A i → B i)
  → (is-equiv₀ : isEquiv (f i0))
  → (is-equiv₁ : isEquiv (f i1))
  → ∀ φ → A φ ≃ B φ
lineEquiv f is-equiv₀ is-equiv₁ φ = λ where
  .fst → f φ
  .snd → isProp→PathP (λ i → isPropIsEquiv (f i)) is-equiv₀ is-equiv₁ φ

ua-unglue-equiv : (e : A ≃ B) → ∀ φ → ua e φ ≃ B
ua-unglue-equiv e φ .fst = ua-unglue e φ
ua-unglue-equiv e φ .snd = isProp→PathP (λ i → isPropIsEquiv (ua-unglue e i)) (equivIsEquiv e) (idIsEquiv _) φ

ua-comp-unglue-equiv : {A B C : Type ℓ} (f : A ≃ B) (g : B ≃ C) → ∀ φ → ua f φ ≃ C
ua-comp-unglue-equiv {C} f g = lineEquiv (λ φ x → equivFun g (ua-unglue f φ x)) (equivIsEquiv (f ∙ₑ g)) (equivIsEquiv g)

secEquiv : (e : A ≃ B) → ∀ (φ : I) → B ≃ B
secEquiv {B} e = lineEquiv (λ φ b → secEq e b φ) (equivIsEquiv (invEquiv e ∙ₑ e)) (idIsEquiv B)

uaCompEquivSquare : ∀ {A B C : Type ℓ} → (f : A ≃ B) (g : B ≃ C) → PathP (λ j → A ≡ ua g j) (ua f) (ua (f ∙ₑ g))
uaCompEquivSquare {ℓ} {A} {B} {C} f g i j = Glue C {φ} system where
  φ : I
  φ = ∂ i ∨ ∂ j

  system : Partial φ (Σ[ T ∈ Type ℓ ] T ≃ C)
  system (i = i0) = ua f j , ua-comp-unglue-equiv f g j
  system (i = i1) = ua (f ∙ₑ g) j , ua-unglue-equiv (f ∙ₑ g) j
  system (j = i0) = A , f ∙ₑ g
  system (j = i1) = ua g i , ua-unglue-equiv g i

uaCompEquiv′ : ∀ {A B C : Type ℓ} → (f : A ≃ B) (g : B ≃ C) → (ua f) ∙ (ua g) ≡ ua (f ∙ₑ g)
uaCompEquiv′ {A} {B} {C} f g = transport (PathP≡compPath (ua f) (ua g) (ua (f ∙ₑ g))) (uaCompEquivSquare f g)

uaInvEquiv′ : {A B : Type ℓ} (e : A ≃ B) → ua (invEquiv e) ≡ sym (ua e)
uaInvEquiv′ {ℓ} {A} {B} e i j = Glue B {φ} system where
  φ : I
  φ = ∂ i ∨ ∂ j

  system : Partial φ (Σ[ T ∈ Type ℓ ] T ≃ B)
  system (i = i0) = ua (invEquiv e) j , ua-comp-unglue-equiv (invEquiv e) e j
  system (i = i1) = ua e (~ j) , ua-unglue-equiv e (~ j)
  system (j = i0) = B , secEquiv e i
  system (j = i1) = A , e

module _ {ℓA ℓB}
  {A : Type ℓA}
  {B₀ B₁ : Type ℓB}
  {e : B₀ ≃ B₁}
  {f₀ : A → B₀}
  {f₁ : A → B₁}
  where
  →ua : (p : ∀ a → equivFun e (f₀ a) ≡ f₁ a) → PathP (λ i → A → ua e i) f₀ f₁
  →ua p i a = ua-gluePath e (p a) i

  →ua⁻ : (p : PathP (λ i → A → ua e i) f₀ f₁) → ∀ a → equivFun e (f₀ a) ≡ f₁ a
  →ua⁻ p a = ua-ungluePath e λ i → p i a

ua→ : ∀ {ℓ ℓ'} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁} {B : (i : I) → Type ℓ'}
  {f₀ : A₀ → B i0} {f₁ : A₁ → B i1}
  → (p : (a : A₀) → PathP B (f₀ a) (f₁ (e .fst a)))
  → PathP (λ i → ua e i → B i) f₀ f₁
ua→ {A₀} {A₁} {e} {B} {f₀} {f₁} h i a = goal i a where module _ (i : I) (a : ua e i) where
  -- Construct the path from f₀ to f₁ as a heterogeneous composition.
  --
  --     (f₀ a₀ : B i0) - - - - - - - - - - - - > (f₁ a₁ : B i1)
  --            ^                                        ^
  --            |                                        |
  --    ~(h a₀) |                                        | f₁ a₁
  --            |                                        |
  --            |                                        |
  -- (f₁ (e a₀) : B i1) ------------------------> (f₁ a₁ : B i1)
  --                     (f₁ (ua-unglue e i a))
  --
  -- The partial elements `(i = i0) ⊢ (a : A₀)` and `(i = i1) ⊢ (a : A₁)`
  -- are denoted a₀ and a₁, respectively:
  a₀ : Partial (~ i) A₀
  a₀ (i = i0) = a

  a₁ : Partial i A₁
  a₁ (i = i1) = a

  Box : (j : I) → Type _
  Box j = B (i ∨ ~ j)

  -- Observe that:
  --  ∙ (i = i0) ⊢ (ua-unglue e i a = (e a) : A₁)
  --  ∙ (i = i1) ⊢ (ua-unglue e i a =   a   : A₁)
  -- Thus we can apply f₁ and obtain a term in `B i1` that reduces to
  -- `f₁ (e a₀)` an `f₁ a₁` when i is i0 or i1, respectively.
  base : Box i0
  base = f₁ (ua-unglue e i a)

  -- The left side of the box connects `f₀ a₀` and `f₁ (e a₀)` via p,
  -- the right side is constantly `f₁ a₁`.
  side : (j : I) → Partial (i ∨ ~ i) (Box j)
  side j (i = i0) = h (a₀ 1=1) (~ j)
  side j (i = i1) = f₁ (a₁ 1=1)

  goal : Box i1
  goal = comp Box side base

isEquiv-ua→ : ∀ {ℓ ℓ'} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁} {B : (i : I) → Type ℓ'}
  → {f₀ : A₀ → B i0} {f₁ : A₁ → B i1}
  → isEquiv (ua→ {e = e} {B} {f₀} {f₁})
isEquiv-ua→ {e} {B} {f₀} {f₁} = {! !}

ua→Equiv : ∀ {ℓ ℓ'} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁} {B : (i : I) → Type ℓ'}
  → {f₀ : A₀ → B i0} {f₁ : A₁ → B i1}
  → ((a : A₀) → PathP B (f₀ a) (f₁ (e .fst a))) ≃ PathP (λ i → ua e i → B i) f₀ f₁
ua→Equiv .fst = ua→
ua→Equiv .snd = isEquiv-ua→

ua→ua : ∀ {ℓ ℓ'} {A₀ A₁ : Type ℓ} {B₀ B₁ : Type ℓ'}
  → {α : A₀ ≃ A₁}
  → {β : B₀ ≃ B₁}
  → {f₀ : A₀ → B₀} {f₁ : A₁ → B₁}
  → (comm : (a₀ : A₀) →  equivFun β (f₀ a₀) ≡ f₁ (equivFun α a₀))
  → PathP (λ i → ua α i → ua β i) f₀ f₁
ua→ua {α} {β} comm = ua→ λ a₀ → ua-gluePath β (comm a₀)

ua→uaEquiv : ∀ {ℓ ℓ'} {A₀ A₁ : Type ℓ} {B₀ B₁ : Type ℓ'}
  → {α : A₀ ≃ A₁}
  → {β : B₀ ≃ B₁}
  → {f₀ : A₀ → B₀} {f₁ : A₁ → B₁}
  → ((a₀ : A₀) →  equivFun β (f₀ a₀) ≡ f₁ (equivFun α a₀)) ≃ PathP (λ i → ua α i → ua β i) f₀ f₁
ua→uaEquiv {A₀} {α} {β} {f₀} {f₁} = equivΠCod lemma ∙ₑ ua→Equiv where
  lemma : (a : A₀) → (equivFun β (f₀ a) ≡ f₁ (equivFun α a)) ≃ PathP (λ i → ua β i) (f₀ a) (f₁ (equivFun α a))
  lemma a = invEquiv (ua-ungluePath-Equiv β)
