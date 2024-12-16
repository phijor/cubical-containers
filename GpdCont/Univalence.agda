module GpdCont.Univalence where

open import GpdCont.Prelude
open import GpdCont.Equiv using (lineEquiv ; secEquiv ; equivΠDomain)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using (PathP≡compPath)
open import Cubical.Foundations.Univalence as UA hiding (ua ; ua→ ; ua→⁻) public
open import Cubical.Foundations.Univalence using (ua-unglue ; unglueIsEquiv ; Glue)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Reflection.StrictEquiv
open import Cubical.Data.Sigma using (ΣPathP ; Σ-contractSnd)

private
  variable
    ℓ : Level
    A B C : Type ℓ

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

ua-unglue-equiv : (e : A ≃ B) → ∀ φ → ua e φ ≃ B
ua-unglue-equiv e φ .fst = ua-unglue e φ
ua-unglue-equiv e φ .snd = isProp→PathP (λ i → isPropIsEquiv (ua-unglue e i)) (equivIsEquiv e) (idIsEquiv _) φ

ua-comp-unglue-equiv : {A B C : Type ℓ} (f : A ≃ B) (g : B ≃ C) → ∀ φ → ua f φ ≃ C
ua-comp-unglue-equiv {C} f g = lineEquiv (λ φ x → equivFun g (ua-unglue f φ x)) (equivIsEquiv (f ∙ₑ g)) (equivIsEquiv g)

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

  →uaEquiv : (∀ a → equivFun e (f₀ a) ≡ f₁ a) ≃ PathP (λ i → A → ua e i) f₀ f₁
  unquoteDef →uaEquiv = defStrictEquiv →uaEquiv →ua →ua⁻

module _ {ℓ} {A₀ A₁ : Type ℓ} (e : A₀ ≃ A₁) where
  ua-gluePtPath : ∀ (a₀ : A₀) → PathP (λ i → ua e i) a₀ (equivFun e a₀)
  ua-gluePtPath a₀ i = ua-gluePt e i a₀

  isContrSingl-ua : ∀ (a₀ : A₀) → isContr (singlP (λ i → ua e i) a₀)
  isContrSingl-ua a₀ .fst = equivFun e a₀ , ua-gluePtPath a₀
  isContrSingl-ua a₀ .snd (a₁ , h) = ΣPathP (p , pᴰ) where

    p : equivFun e a₀ ≡ a₁
    p = ua-ungluePath e h

    T : (j : I) → Partial (∂ j) (Type _)
    T j (j = i0) = A₀
    T j (j = i1) = A₁

    system : (i j : I) → PartialP (∂ j) (T j)
    system i j (j = i0) = a₀
    system i j (j = i1) = p i

    pᴰ : SquareP (λ i j → ua e j) (ua-gluePtPath a₀) h (refl {x = a₀}) (ua-ungluePath e h)
    pᴰ i j = glue {φ = ∂ j} {T = T j} (system i j) (p (i ∧ j))

module UA→ {ℓ ℓ'}
  {A₀ A₁ : Type ℓ}
  {e : A₀ ≃ A₁}
  {B : (i : I) → Type ℓ'}
  {f₀ : A₀ → B i0} {f₁ : A₁ → B i1}
  where
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
  private
    ua→-Box : (i j : I) → Type ℓ'
    ua→-Box i j = B (i ∨ ~ j)

  -- Above we assume (a : ua e i), and the partial elements `(i = i0) ⊢ (a : A₀)`
  -- and `(i = i1) ⊢ (a : A₁)` are denoted a₀ and a₁, respectively:
  module _
    (h : (a : A₀) → PathP B (f₀ a) (f₁ (e .fst a)))
    (i : I)
    (a : ua e i)
    where
    private
      a₀ : Partial (~ i) A₀
      a₀ (i = i0) = a

      a₁ : Partial i A₁
      a₁ (i = i1) = a

    -- The left side of the box connects `f₀ a₀` and `f₁ (e a₀)` via h,
    -- the right side is constantly `f₁ a₁`.
    ua→-side : (j : I) → Partial (i ∨ ~ i) (ua→-Box i j)
    ua→-side j (i = i0) = h (a₀ 1=1) (~ j)
    ua→-side j (i = i1) = f₁ (a₁ 1=1)


  ua→-base : PathP (λ i → (a : ua e i) → B i1) (f₁ ∘ (equivFun e)) f₁
  ua→-base i a = f₁ (ua-unglue e i a)

  module _
    (h : (a : A₀) → PathP B (f₀ a) (f₁ (e .fst a)))
    where
    ua→ : PathP (λ i → ua e i → B i) f₀ f₁
    ua→ i a = comp (ua→-Box i) (ua→-side h i a) (ua→-base i a)

    ua→-filler : SquareP (λ i j → ua e i → B (i ∨ ~ j)) (symP (funExt h)) (refl {x = f₁}) ua→-base ua→
    ua→-filler i j a = fill
      (λ j → ua→-Box i j)
      {φ = ∂ i}
      (ua→-side h i a)
      (inS (ua→-base i a))
      j

  ua→⁻ : PathP (λ i → ua e i → B i) f₀ f₁ → ((a : A₀) → PathP B (f₀ a) (f₁ (e .fst a)))
  ua→⁻ pᴰ a i = pᴰ i (UA.ua-gluePt e i a)

  ua→⁻Equiv' : PathP (λ i → ua e i → B i) f₀ f₁ ≃ ((a : A₀) → PathP B (f₀ a) (f₁ (e .fst a)))
  ua→⁻Equiv' =
    PathP (λ i → ua e i → B i) f₀ f₁ ≃⟨ invEquiv funExtNonDepEquiv ⟩
    ({x₀ : A₀} {x₁ : A₁} → PathP (λ i → ua e i) x₀ x₁ → PathP B (f₀ x₀) (f₁ x₁)) ≃⟨ shuffle ⟩
    ((x : Σ[ x₀ ∈ A₀ ] (singlP (λ i → ua e i) x₀)) → PathP B (f₀ (x .fst)) (f₁ (x .snd .fst))) ≃⟨ equivΠDomain (invEquiv (Σ-contractSnd (isContrSingl-ua e))) ⟩
    ((a : A₀) → PathP B (f₀ a) (f₁ (equivFun e a))) ≃∎
    where
    shuffle-iso : Iso
      ({x₀ : A₀} {x₁ : A₁} → PathP (λ i → ua e i) x₀ x₁ → PathP B (f₀ x₀) (f₁ x₁))
      ((x : Σ[ x₀ ∈ A₀ ] (singlP (λ i → ua e i) x₀)) → PathP B (f₀ (x .fst)) (f₁ (x .snd .fst)))
    shuffle-iso .Iso.fun f (x₀ , x₁ , p) = f {x₀} {x₁} p
    shuffle-iso .Iso.inv f {x₀} {x₁} p = f (x₀ , x₁ , p)
    shuffle-iso .Iso.rightInv _ = refl
    shuffle-iso .Iso.leftInv _ = refl

    shuffle : _ ≃ _
    shuffle = strictIsoToEquiv shuffle-iso

  ua→⁻Equiv : PathP (λ i → ua e i → B i) f₀ f₁ ≃ ((a : A₀) → PathP B (f₀ a) (f₁ (e .fst a)))
  ua→⁻Equiv .fst = ua→⁻
  ua→⁻Equiv .snd = equivIsEquiv ua→⁻Equiv'

  -- TODO: Have a look at transport-filler-ua in Cubical.Foundations.Transport
  ua→′Equiv : ((a : A₀) → PathP B (f₀ a) (f₁ (e .fst a))) ≃ PathP (λ i → ua e i → B i) f₀ f₁
  ua→′Equiv = invEquiv ua→⁻Equiv

  ua→′ : ((a : A₀) → PathP B (f₀ a) (f₁ (e .fst a))) → PathP (λ i → ua e i → B i) f₀ f₁
  ua→′ = equivFun ua→′Equiv

open UA→ hiding (ua→ ; ua→-filler ; ua→-side ; ua→-base) renaming (ua→′ to ua→ ; ua→′Equiv to ua→Equiv) public

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
