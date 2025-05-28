module GpdCont.StrictGroupoid.HomotopyGroup where

open import GpdCont.Prelude
open import GpdCont.Connectivity
open import GpdCont.SetTruncation as ST using (isConnected-fiber-∣-∣₂)

open import GpdCont.StrictGroupoid.Base
open import GpdCont.StrictGroupoid.Morphism

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed.Base as Pointed using (Pointed)
open import Cubical.Foundations.Equiv.Properties using (hasSection)
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.Wedge as Wedge using (_⋁_)

private
  variable
    ℓ : Level

isHGroup : StrictGroupoid ℓ → Type ℓ
isHGroup G = isPathConnected ⟨ G ⟩

isPropIsHGroup : (G : StrictGroupoid ℓ) → isProp (isHGroup G)
isPropIsHGroup G = isPropIsPathConnected ⟨ G ⟩

hGroup : (ℓ : Level) → Type (ℓ-suc ℓ)
hGroup ℓ = Σ[ G ∈ StrictGroupoid ℓ ] isHGroup G

module hGroup (G : hGroup ℓ) where
  open StrictGroupoidStr (str (G .fst)) public

  is-connected : isPathConnected ⟨ G .fst ⟩
  is-connected = G .snd

  center : ∥ ⟨ G .fst ⟩ ∥₂
  center = is-connected .fst

  pt₀ : ⟨ G .fst ⟩
  pt₀ = pt center

  asPointed : Pointed ℓ
  asPointed .fst = ⟨ G .fst ⟩
  asPointed .snd = pt₀

  asGroupoid : hGroupoid ℓ
  asGroupoid .fst = ⟨ G . fst ⟩
  asGroupoid .snd = is-groupoid


hGroup≡ : ∀ {G H : hGroup ℓ} → G .fst ≡ H .fst → G ≡ H
hGroup≡ = Σ≡Prop isPropIsHGroup

hGroupHom : (G H : hGroup ℓ) → Type _
hGroupHom (G , _) (H , _) = StrictFun G H

pointedConnectedGroupoid→hGroup : ∀ (G : Type ℓ)
  → (g₀ : G)
  → isPathConnected G
  → isGroupoid G
  → hGroup ℓ
pointedConnectedGroupoid→hGroup G g₀ is-conn-G is-groupoid-G = G* where
  G* : hGroup _
  G* .fst .fst = G
  G* .fst .snd .StrictGroupoidStr.is-groupoid = is-groupoid-G
  G* .fst .snd .StrictGroupoidStr.pt = const g₀
  G* .fst .snd .StrictGroupoidStr.pt-section = isContr→isProp is-conn-G ∣ g₀ ∣₂
  G* .snd = is-conn-G

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

Aut∙ : (A : Pointed ℓ) → isGroupoid ⟨ A ⟩ → hGroup _
Aut∙ (A , a₀) is-groupoid-A = Aut (A , is-groupoid-A) a₀

ΠGroup : ∀ {ℓK} (K : Type ℓK) (G : K → hGroup ℓ) → hGroup (ℓ-max ℓ ℓK)
ΠGroup K G* = Aut ΠG Πpt
  where
    G : K → Type _
    G k = ⟨ G* k .fst ⟩

    module G k = hGroup (G* k)

    ΠG : hGroupoid _
    ΠG .fst = ∀ k → G k
    ΠG .snd = isGroupoidΠ G.is-groupoid

    Πpt : ∀ k → G k
    Πpt = G.pt₀

proj : ∀ {K : Type ℓ} (G : K → hGroup ℓ) → ∀ k → hGroupHom (ΠGroup K G) (G k)
proj _ k .fst (f , f-strict) = f k
proj {K} G k .snd = funExt (ST.elim (λ _ → G.is-groupoid k _ _) $ uncurry is-strict-π) where
  module G k = hGroup (G k)
  open import Cubical.HITs.PropositionalTruncation.Monad

  abstract
    is-strict-π' : (f : (k : K) → ⟨ G k .fst ⟩) → f ≡ G.pt₀ → ∣ f k ∣₂ ≡ G.center k
    is-strict-π' f f≡pt =
      ∣ f k ∣₂ ≡[ i ]⟨ ∣ f≡pt i k ∣₂ ⟩
      ∣ G.pt k (G.center k) ∣₂ ≡⟨ G.pt-section k (G.center k) ⟩
      G.center k ∎

  is-strict-π : (f : (k : K) → ⟨ G k .fst ⟩) → (f-strict : ∣ f ∣₂ ≡ ∣ G.pt₀ ∣₂) → G.pt k ∣ f k ∣₂ ≡ G.pt₀ k
  is-strict-π f f-strict = cong (G.pt k) $ ST.pathSetTrunc→recProp (ST.isSetSetTrunc _ _) (is-strict-π' f) f-strict

isProductΠGroup : ∀ {ℓ} (K : Type ℓ) (G : K → hGroup ℓ) (H : hGroup ℓ) → isEquiv (λ (f : hGroupHom H (ΠGroup K G)) (k : K) → compStrict (H .fst) _ (G k .fst) f (proj G k))
isProductΠGroup K G H .equiv-proof fs .fst = {! compStrict _ _ _  !} , {! !}
isProductΠGroup K G H .equiv-proof fs .snd = {! !}

private
  test : (K : Type ℓ) (G : K → hGroup ℓ) → ⟨ ΠGroup K G .fst ⟩ ≡ Σ ((k : K) → fst (G k .fst)) (λ x → ∣ x ∣₂ ≡ ∣ (λ k → StrictGroupoidStr.pt (snd (G k .fst)) (G k .snd .fst)) ∣₂)
  test K G = refl

-- ∗ = \ast
_∗_ : (G H : hGroup ℓ) → hGroup ℓ
G ∗ H = Aut∙ G⋁H is-groupoid-G⋁H where
  module G = hGroup G
  module H = hGroup H

  G⋁H : Pointed _
  G⋁H = G.asPointed Wedge.⋁∙ₗ H.asPointed

  is-groupoid-G⋁H : isGroupoid ⟨ G⋁H ⟩
  is-groupoid-G⋁H = {! !}

⨁Group : (K : Type ℓ) (G : K → hGroup ℓ) → hGroup ℓ
⨁Group K G = Aut∙ (Wedge.⋁gen∙ K (hGroup.asPointed ∘ G)) is-groupoid-⨁G where
  abstract
    is-groupoid-⨁G : isGroupoid ⟨ Wedge.⋁gen∙ K (hGroup.asPointed ∘ G) ⟩
    is-groupoid-⨁G = {! !}
