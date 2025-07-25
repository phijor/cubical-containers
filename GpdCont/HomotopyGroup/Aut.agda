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
open import Cubical.Foundations.Pointed.Base as Pointed using (Pointed)
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  variable
    ℓ ℓ′ : Level

Aut : (A : hGroupoid ℓ) (a₀ : ⟨ A ⟩) → hGroup _
Aut (A , is-groupoid-A) a₀ = pointedConnectedGroupoid→hGroup G g₀ conn-G is-groupoid-G where
  G : Type _
  G = fiber ∣_∣₂ ∣ a₀ ∣₂

  g₀ : G
  g₀ .fst = a₀
  g₀ .snd = refl′ ∣ a₀ ∣₂

  conn-G : isPathConnected G
  conn-G = isConnected-fiber-∣-∣₂ ∣ a₀ ∣₂

  is-groupoid-G : isGroupoid G
  is-groupoid-G = isGroupoidΣ is-groupoid-A λ a → isProp→isOfHLevelSuc 2 (ST.isSetSetTrunc ∣ a ∣₂ ∣ a₀ ∣₂)

module _ (A : hGroupoid ℓ) (a₀ : ⟨ A ⟩) where
  AutEmbedding : ⟨ Aut A a₀ ⟩ᵗ ↪ ⟨ A ⟩
  AutEmbedding = EmbeddingΣProp λ a → ST.isSetSetTrunc ∣ a ∣₂ ∣ a₀ ∣₂

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
  λ a → isContr→isContrPath (ST.isContr→isContrSetTrunc is-contr-A) ∣ a ∣₂ ∣ a₀ ∣₂

aut-map : (A : hGroupoid ℓ) {a₀ : ⟨ A ⟩} (B : hGroupoid ℓ′) {b₀ : ⟨ B ⟩}
  → (f : ⟨ A ⟩ → ⟨ B ⟩)
  → (pres-pt : f a₀ ≡ b₀)
  → hGroupHom (Aut A a₀) (Aut B b₀)
aut-map A {a₀} B {b₀} f pres-pt = mkHGroupHom (Aut A _) (Aut B _) f* pres-pt-f* module aut-map where
  pres-conn : ∀ a → ∣ a ∣₂ ≡ ∣ a₀ ∣₂ → ∣ f a ∣₂ ≡ ∣ b₀ ∣₂
  pres-conn a p = ST.merePath→pathSetTrunc $ PT.map (λ a≡a₀ → cong f a≡a₀ ∙ pres-pt) (ST.pathSetTrunc→merePath p)

  f* : ⟨ Aut A _ ⟩ᵗ → ⟨ Aut B _ ⟩ᵗ
  f* = Σ-map f pres-conn

  -- TODO: The path in the second component can be given explicitly.
  -- We can derive (pres-conn a₀ refl ≡ pres-pt).
  pres-pt-f* : f* (a₀ , refl) ≡ (b₀ , refl)
  pres-pt-f* = Σ≡Prop (λ _ → ST.isSetSetTrunc _ _) pres-pt

isOfHLevelSucAutMap : (n : HLevel)
  → (A : hGroupoid ℓ) {a₀ : ⟨ A ⟩} (B : hGroupoid ℓ′) {b₀ : ⟨ B ⟩}
  → (f : ⟨ A ⟩ → ⟨ B ⟩)
  → (pres-pt : f a₀ ≡ b₀)
  → isOfHLevelFun (suc n) f
  → isOfHLevelFun (suc n) (aut-map A B f pres-pt .fst)
isOfHLevelSucAutMap n A {a₀} B {b₀} f pres-pt is-trunc-f = isOfHLevelFunΣMap (suc n) is-trunc-f goal where
  goal : ∀ a → isOfHLevelFun (suc n) (aut-map.pres-conn A B f pres-pt a)
  goal a ∣fa≡b₀∣ = isOfHLevelΣ (suc n)
    (isProp→isOfHLevelSuc n (ST.isSetSetTrunc _ _))
    λ p → (isContr→isOfHLevel (suc n) (isProp→isContrPath (ST.isSetSetTrunc _ _) _ _))

isTruncFiberPt→isTruncAutMap : (n : HLevel)
  → (A : hGroupoid ℓ) {a₀ : ⟨ A ⟩} (B : hGroupoid ℓ′) {b₀ : ⟨ B ⟩}
  → (f : ⟨ A ⟩ → ⟨ B ⟩)
  → (pres-pt : f a₀ ≡ b₀)
  → isOfHLevel (suc n) (fiber f b₀)
  → isOfHLevelFun (suc n) (aut-map A B f pres-pt .fst)
isTruncFiberPt→isTruncAutMap n A {a₀} B {b₀} f pres-pt is-trunc-fib-pt = hGroup.elimProp (Aut B _)
  (λ _ → isPropIsOfHLevel (suc n))
  (isOfHLevelRespectEquiv (suc n) fiber-equiv is-trunc-fiber-sub)
  where
    fiber-equiv : (Σ[ (a , _) ∈ fiber f b₀ ] ST.∣ a ∣₂ ≡ ST.∣ a₀ ∣₂) ≃ fiber (aut-map A B f pres-pt .fst) (b₀ , refl)
    fiber-equiv =
      Σ[ (a , _) ∈ fiber f b₀ ] ST.∣ a ∣₂ ≡ ST.∣ a₀ ∣₂
        ≃⟨ strictEquiv (λ ((a , p) , a-conn) → ((a , a-conn) , p)) (λ ((a , a-conn) , p) → ((a , p) , a-conn)) ⟩
      Σ[ (a , a-conn) ∈ ⟨ Aut A _ ⟩ᵗ ] f a ≡ b₀
        ≃⟨ Σ-cong-equiv-snd (λ a' → invEquiv $ (cong fst) , isEmbeddingFstΣProp (λ _ → ST.isSetSetTrunc _ _)) ⟩
      Σ[ (a , a-conn) ∈ ⟨ Aut A _ ⟩ᵗ ] (f a , _) ≡ (b₀ , refl)
        ≃∎

    is-trunc-fiber-sub : isOfHLevel (suc n) (Σ[ (a , _) ∈ fiber f b₀ ] ST.∣ a ∣₂ ≡ ST.∣ a₀ ∣₂)
    is-trunc-fiber-sub = isOfHLevelΣ (suc n) is-trunc-fib-pt λ _ → isProp→isOfHLevelSuc n $ ST.isSetSetTrunc _ _

AutEquiv : (A : hGroupoid ℓ) {a₀ : ⟨ A ⟩} (B : hGroupoid ℓ′) {b₀ : ⟨ B ⟩}
  → (e : ⟨ A ⟩ ≃ ⟨ B ⟩)
  → (pres-pt : equivFun e a₀ ≡ b₀)
  → hGroupEquiv (Aut A a₀) (Aut B b₀)
AutEquiv A {a₀} B {b₀} e pres-pt = mkHGroupEquiv (Aut A _) (Aut B _) aut-equiv pres-pt-aut where
  hey : ∀ a → ∣ a ∣₂ ≡ ∣ a₀ ∣₂ → ∣ equivFun e a ∣₂ ≡ ∣ b₀ ∣₂
  hey a p = ST.merePath→pathSetTrunc $ PT.map (λ a≡a₀ → cong (equivFun e) a≡a₀ ∙ pres-pt) (ST.pathSetTrunc→merePath p)

  hoo : ∀ a → ∣ equivFun e a ∣₂ ≡ ∣ b₀ ∣₂ → ∣ a ∣₂ ≡ ∣ a₀ ∣₂
  hoo a p = ST.merePath→pathSetTrunc $ PT.map (λ ea≡b₀ → invEq (congEquiv e) (ea≡b₀ ∙ sym pres-pt)) (ST.pathSetTrunc→merePath p)

  aut-equiv : ⟨ Aut A _ ⟩ᵗ ≃ ⟨ Aut B _ ⟩ᵗ
  aut-equiv = Σ-cong-equiv e λ a → propBiimpl→Equiv (ST.isSetSetTrunc _ _) (ST.isSetSetTrunc _ _) (hey a) (hoo a)

  pres-pt-aut : equivFun aut-equiv (a₀ , refl) ≡ (b₀ , refl)
  pres-pt-aut = Σ≡Prop (λ _ → ST.isSetSetTrunc _ _) pres-pt
