module GpdCont.HomotopyGroup.Aut where

open import GpdCont.HomotopyGroup.Base
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
