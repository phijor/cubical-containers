module GpdCont.HomotopyGroup.Aut where

open import GpdCont.HomotopyGroup.Base
open import GpdCont.HomotopyGroup.Morphism
open import GpdCont.HomotopyGroup.Equiv

open import GpdCont.Prelude
open import GpdCont.Connectivity
open import GpdCont.Embedding
open import GpdCont.SetTruncation as ST using (isConnected-fiber-∣-∣₂)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed.Base as Pointed using (Pointed)
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)

private
  variable
    ℓ ℓ′ : Level

Aut : (A : hGroupoid ℓ) (a₀ : ⟨ A ⟩) → hGroup ℓ
Aut (A , is-groupoid-A) a₀ = pointedConnectedGroupoid→hGroup G g₀ conn-G is-groupoid-G module Aut where
  G : Type _
  G = Σ[ a ∈ A ] ∥ a ≡ a₀ ∥₁

  g₀ : G
  g₀ .fst = a₀
  g₀ .snd = ∣ refl′ a₀ ∣₁

  opaque
    conn-G : isPathConnected G
    conn-G = inh×merePath→isPathConnected g₀ λ where
      (a , mere-path) → PT.map (λ a≡a₀ → Σ≡Prop (λ _ → PT.isPropPropTrunc) (sym a≡a₀)) mere-path

    is-groupoid-G : isGroupoid G
    is-groupoid-G = isGroupoidΣ is-groupoid-A λ a → isProp→isOfHLevelSuc 2 PT.isPropPropTrunc
{-# INJECTIVE_FOR_INFERENCE Aut #-}

pattern aut a = (a , _)

module _ (A : hGroupoid ℓ) (a₀ : ⟨ A ⟩) where
  AutEmbedding : ⟨ Aut A a₀ ⟩ᵗ ↪ ⟨ A ⟩
  AutEmbedding = EmbeddingΣProp λ a → PT.isPropPropTrunc

  AutPathEquiv : ∀ (x y : ⟨ Aut A a₀ ⟩ᵗ) → (x ≡ y) ≃ Path ⟨ A ⟩ (x .fst) (y .fst)
  AutPathEquiv x y .fst = cong fst
  AutPathEquiv x y .snd = AutEmbedding .snd x y

  AutPath : {x y : ⟨ Aut A a₀ ⟩ᵗ} → Path ⟨ A ⟩ (x .fst) (y .fst) → (x ≡ y)
  AutPath = invEq (AutPathEquiv _ _)

Aut∙ : (A : Pointed ℓ) → isGroupoid ⟨ A ⟩ → hGroup _
Aut∙ (A , a₀) is-groupoid-A = Aut (A , is-groupoid-A) a₀

Sym : (X : hSet ℓ) → hGroup (ℓ-suc ℓ)
Sym X = Aut (hSet _ , isGroupoidHSet) X

isContrAut : (A : hGroupoid ℓ) (a₀ : ⟨ A ⟩)
  → isContr ⟨ A ⟩
  → isContr ⟨ Aut A a₀ ⟩ᵗ
isContrAut (A , _) a₀ is-contr-A = isContrΣ
  is-contr-A
  λ a → inhProp→isContr ∣ isContr→isProp is-contr-A a a₀ ∣₁ PT.isPropPropTrunc

aut-map : (A : hGroupoid ℓ) {a₀ : ⟨ A ⟩} (B : hGroupoid ℓ′) {b₀ : ⟨ B ⟩}
  → (f : ⟨ A ⟩ → ⟨ B ⟩)
  → (pres-pt : f a₀ ≡ b₀)
  → hGroupHom (Aut A a₀) (Aut B b₀)
aut-map A {a₀} B {b₀} f pres-pt = mkHGroupHom f* pres-pt-f* module aut-map where
  pres-conn : ∀ a → ∥ a ≡ a₀ ∥₁ → ∥ f a ≡ b₀ ∥₁
  pres-conn a = PT.map (λ a≡a₀ → cong f a≡a₀ ∙ pres-pt)

  f* : ⟨ Aut A _ ⟩ᵗ → ⟨ Aut B _ ⟩ᵗ
  f* = Σ-map f pres-conn

  pres-pt-f* : f* (a₀ , ∣ refl ∣₁) ≡ (b₀ , ∣ refl ∣₁)
  pres-pt-f* = ΣPathP λ where
    .fst → pres-pt
    .snd → congP (λ _ → ∣_∣₁) (subst (λ - → PathP (λ i → pres-pt i ≡ b₀) - refl) (lUnit pres-pt) λ i j → pres-pt (i ∨ j))

isOfHLevelSucAutMap : (n : HLevel)
  → (A : hGroupoid ℓ) {a₀ : ⟨ A ⟩} (B : hGroupoid ℓ′) {b₀ : ⟨ B ⟩}
  → (f : ⟨ A ⟩ → ⟨ B ⟩)
  → (pres-pt : f a₀ ≡ b₀)
  → isOfHLevelFun (suc n) f
  → isOfHLevelFun (suc n) (aut-map A B f pres-pt .hGroupHom.fun)
isOfHLevelSucAutMap n A {a₀} B {b₀} f pres-pt is-trunc-f = isOfHLevelFunΣMap (suc n) is-trunc-f goal where
  goal : ∀ a → isOfHLevelFun (suc n) (aut-map.pres-conn A B f pres-pt a)
  goal a ∣fa≡b₀∣ = isOfHLevelΣ (suc n)
    (isProp→isOfHLevelSuc n PT.isPropPropTrunc)
    λ p → (isContr→isOfHLevel (suc n) (isProp→isContrPath PT.isPropPropTrunc _ _))

isTruncFiberPt→isTruncAutMap : (n : HLevel)
  → (A : hGroupoid ℓ) {a₀ : ⟨ A ⟩} (B : hGroupoid ℓ′) {b₀ : ⟨ B ⟩}
  → (f : ⟨ A ⟩ → ⟨ B ⟩)
  → (pres-pt : f a₀ ≡ b₀)
  → isOfHLevel (suc n) (fiber f b₀)
  → isOfHLevelFun (suc n) (aut-map A B f pres-pt .hGroupHom.fun)
isTruncFiberPt→isTruncAutMap n A {a₀} B {b₀} f pres-pt is-trunc-fib-pt = hGroup.elimProp (Aut B _)
  (λ _ → isPropIsOfHLevel (suc n))
  (isOfHLevelRespectEquiv (suc n) fiber-equiv is-trunc-fiber-sub)
  where
    fiber-equiv : (Σ[ (a , _) ∈ fiber f b₀ ] ∥ a ≡ a₀ ∥₁) ≃ fiber (aut-map A B f pres-pt .hGroupHom.fun) (b₀ , ∣ refl ∣₁)
    fiber-equiv =
      Σ[ (a , _) ∈ fiber f b₀ ] ∥ a ≡ a₀ ∥₁
        ≃⟨ strictEquiv (λ ((a , p) , a-conn) → ((a , a-conn) , p)) (λ ((a , a-conn) , p) → ((a , p) , a-conn)) ⟩
      Σ[ (a , a-conn) ∈ ⟨ Aut A _ ⟩ᵗ ] f a ≡ b₀
        ≃⟨ Σ-cong-equiv-snd (λ a' → invEquiv $ (cong fst) , isEmbeddingFstΣProp (λ _ → PT.isPropPropTrunc)) ⟩
      Σ[ (a , a-conn) ∈ ⟨ Aut A _ ⟩ᵗ ] (f a , _) ≡ (b₀ , ∣ refl ∣₁)
        ≃∎

    is-trunc-fiber-sub : isOfHLevel (suc n) (Σ[ (a , _) ∈ fiber f b₀ ] ∥ a ≡ a₀ ∥₁)
    is-trunc-fiber-sub = isOfHLevelΣ (suc n) is-trunc-fib-pt λ _ → isProp→isOfHLevelSuc n PT.isPropPropTrunc

AutEquiv : (A : hGroupoid ℓ) {a₀ : ⟨ A ⟩} (B : hGroupoid ℓ′) {b₀ : ⟨ B ⟩}
  → (e : ⟨ A ⟩ ≃ ⟨ B ⟩)
  → (pres-pt : equivFun e a₀ ≡ b₀)
  → hGroupEquiv (Aut A a₀) (Aut B b₀)
AutEquiv A {a₀} B {b₀} e pres-pt = mkHGroupEquiv (Aut A a₀) (Aut B b₀) aut-equiv pres-pt-aut where
  pres⁺ : ∀ a → ∥ a ≡ a₀ ∥₁ → ∥ equivFun e a ≡ b₀ ∥₁
  pres⁺ a = PT.map (λ a≡a₀ → cong (equivFun e) a≡a₀ ∙ pres-pt)

  pres⁻ : ∀ a → ∥ equivFun e a ≡ b₀ ∥₁ → ∥ a ≡ a₀ ∥₁
  pres⁻ a = PT.map (λ ea≡b₀ → invEq (congEquiv e) (ea≡b₀ ∙ sym pres-pt))

  aut-equiv : ⟨ Aut A _ ⟩ᵗ ≃ ⟨ Aut B _ ⟩ᵗ
  aut-equiv = Σ-cong-equiv e λ a → propBiimpl→Equiv PT.isPropPropTrunc PT.isPropPropTrunc (pres⁺ a) (pres⁻ a)

  pres-pt-aut : equivFun aut-equiv (a₀ , ∣ refl ∣₁) ≡ (b₀ , ∣ refl ∣₁)
  pres-pt-aut = Σ≡Prop (λ _ → PT.isPropPropTrunc) pres-pt
{-# INJECTIVE_FOR_INFERENCE AutEquiv #-}
