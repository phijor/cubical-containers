module GpdCont.HomotopyGroup.Action where

open import GpdCont.Prelude
open import GpdCont.Connectivity
open import GpdCont.Embedding
open import GpdCont.HomotopySet
import      GpdCont.SetTruncation as ST

open import GpdCont.HomotopyGroup.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)


private
  variable
    ℓ ℓX ℓY : Level

hAction : (ℓX : Level) → hGroup ℓ → Type _
hAction ℓX G = ⟨ G ⟩ᵗ → hSet ℓX

mereEquivAction : (G : hGroup ℓ) (X : hAction ℓX G) → (g : ⟨ G ⟩ᵗ) → ∥ ⟨ X (hGroup.pt₀ G) ⟩ ≃ ⟨ X g ⟩ ∥₁
mereEquivAction G X g = PT.map (substEquiv (λ g → ⟨ X g ⟩)) $ hGroup.mere-path G g

isFaithful : (G : hGroup ℓ) (X : hAction ℓX G) → Type _
isFaithful G X = isOfHLevelFun 2 X

isPropIsFaithful : (G : hGroup ℓ) (X : hAction ℓX G) → isProp (isFaithful G X)
isPropIsFaithful G X = isPropΠ λ _ → isPropIsSet

Pr' : (G : hGroup ℓ) → ⟨ G ⟩ᵗ → hAction ℓ G
Pr' G g₀ g .fst = g₀ ≡ g
Pr' G g₀ g .snd = hGroup.is-groupoid G g₀ g

Pr : (G : hGroup ℓ) → hAction ℓ G
Pr G = Pr' G $ hGroup.pt₀ G

Pr* : (G : hGroup ℓ) → ⟨ G ⟩ᵗ → Σ[ X ∈ hAction ℓ G ] ∥ Pr G ≡ X ∥₁
Pr* G g₀ .fst = Pr' G g₀
Pr* G g₀ .snd = PT.map (λ p → funExt λ g → hSet≡ (cong (_≡ g) p)) (hGroup.mere-path G g₀)

-- Pr⁻ : (G : hGroup ℓ) → Σ[ X ∈ hAction ℓ G ] ∥ Pr G ≡ X ∥₁ → ⟨ G ⟩ᵗ
-- Pr⁻ G = uncurry λ X → PT.rec→Gpd {! !} (λ h → {! h ≡$ hGroup.pt₀ G !}) (record { link = {! !} ; coh₁ = {! !} })

-- yonedaPr≃ : (G : hGroup ℓ) (g h : ⟨ G ⟩ᵗ) → (g ≡ h) ≃ (Pr* G g ≡ Pr* G h)
-- yonedaPr≃ G g h = {! !}
--   -- (g ≡ h) ≃⟨ {! !} ⟩
--   -- ((G.pt₀ ≡ g) ≡ (G.pt₀ ≡ h)) ≃⟨ hSet≡Equiv ⟩
--   -- (Pr G g ≡ Pr G h) ≃∎
--   -- where module G = hGroup G


-- yonedaPr : (G : hGroup ℓ) (g h : ⟨ G ⟩ᵗ) → isEquiv (λ (p : g ≡ h) → cong (Pr* G) p)
-- yonedaPr G g h = isoToIsEquiv λ where
--   .Iso.fun → _
--   .Iso.inv x → {! cong (fst) x !}
--   .Iso.leftInv → {! !}
--   .Iso.rightInv → {! !}

-- ???
isFaithfulPr : (G : hGroup ℓ) → isFaithful G (Pr G)
isFaithfulPr G = ST.isEmbeddingCong→hasSetFibers (Pr G) λ g h → injEmbedding (isOfHLevelPath' 2 isGroupoidHSet _ _) (Pr⁻ g h _ _) where
  module G = hGroup G
  Pr⁻ : (g h : ⟨ G ⟩ᵗ) → (p q : g ≡ h) → cong (Pr G) p ≡ cong (Pr G) q → p ≡ q
  Pr⁻ g h p q sq = {! !} where
    sq' : Square (λ i → G.pt₀ ≡ p i) (λ i → G.pt₀ ≡ q i) refl refl
    sq' i j = ⟨ sq i j ⟩
  -- isOfHLevelFunOfImage→isOfHLevelFun 1 _ (G.elimProp {! !} goal) where
  -- module G = hGroup G
  -- foo : (fiber (Pr G) (Pr G G.pt₀)) ≃ {! !}
  -- foo =
  --   (fiber (Pr G) (Pr G G.pt₀)) ≃⟨ {! !} ⟩
  --   Σ[ g ∈ ⟨ G ⟩ᵗ ] (Pr G g) ≡ (Pr G G.pt₀) ≃⟨ {! !} ⟩
  --   Σ[ g ∈ ⟨ G ⟩ᵗ ] (G.pt₀ ≡ g) ≡ (G.pt₀ ≡ G.pt₀) ≃⟨ {! !} {- Yoneda? -} ⟩
  --   Σ[ g ∈ ⟨ G ⟩ᵗ ] g ≡ G.pt₀ ≃⟨ {! !} ⟩
  --   singl G.pt₀ ≃∎

  -- goal : (x y : fiber (Pr G) (Pr G G.pt₀)) → isProp (x ≡ y)
  -- goal = {! !}

∫ : (G : hGroup ℓ) (X : hAction ℓX G) → hGroupoid (ℓ-max ℓ ℓX)
∫ G X .fst = Σ[ g ∈ ⟨ G ⟩ᵗ ] ⟨ X g ⟩
∫ G X .snd = isGroupoidΣ (hGroup.is-groupoid G) λ g → isSet→isGroupoid $ str $ X g

isTransitive : (G : hGroup ℓ) (X : hAction ℓX G) → Type _
isTransitive G X = isPathConnected ⟨ ∫ G X ⟩

isPropIsTransitive : (G : hGroup ℓ) (X : hAction ℓX G) → isProp (isTransitive G X)
isPropIsTransitive G X = isPropIsPathConnected _

precompAction : ∀ {ℓ′} (G : hGroup ℓ) (X : hAction ℓX G) (Y : hSet ℓ′) → hAction (ℓ-max ℓX ℓ′) G
precompAction G X Y = λ g → X g →Set Y

precompAction∫ : ∀ {ℓ′} (G : hGroup ℓ) (X : hAction ℓX G) (Y : hSet ℓ′)
  → ⟨ ∫ G (precompAction G X Y) ⟩ ≃ {! !}
precompAction∫ G X Y =
  Σ[ g ∈ ⟨ G ⟩ᵗ ] (⟨ X g ⟩ → ⟨ Y ⟩) ≃⟨ {! !} ⟩
  {! !} ≃∎

module _ (G : hGroup ℓ) (X : hAction ℓX G) (Y : hAction ℓY G) where
  private module G = hGroup G

  hActionHom : Type _
  hActionHom = ∀ g → ⟨ X g ⟩ → ⟨ Y g ⟩

  ev : {g : ⟨ G ⟩ᵗ} (x : ⟨ X g ⟩) → hActionHom → ⟨ Y g ⟩
  ev {g} x f = f g x

  isTransitive→isEmbeddingEv : isTransitive G X → ∀ {g₀ : ⟨ G ⟩ᵗ} (x₀ : ⟨ X g₀ ⟩) → isOfHLevelFun 1 (ev x₀)
  isTransitive→isEmbeddingEv is-transitive-X {g₀} x₀ y (f₀ , p₀) (f₁ , p₁) = goal where
    p : f₀ g₀ x₀ ≡ f₁ g₀ x₀
    p = p₀ ∙ sym p₁

    -- Assuming some path from (g₀ , x₀) to (g , x) exists, we can equate f₀ and f₁:
    path-ext-conn : ∀ g x
      → (pᵍ : g₀ ≡ g)
      → (pˣ : PathP (λ i → ⟨ X (pᵍ i) ⟩) x₀ x)
      → f₀ g x ≡ f₁ g x
    path-ext-conn g x pᵍ pˣ = goal where
      -- Substituting under f₀ and f₁, we get paths in Y over pᵍ:
      p₀′ : PathP (λ i → ⟨ Y (pᵍ i) ⟩) (f₀ g₀ x₀) (f₀ g x)
      p₀′ = cong₂ f₀ pᵍ pˣ
      p₁′ : PathP (λ i → ⟨ Y (pᵍ i) ⟩) (f₁ g₀ x₀) (f₁ g x)
      p₁′ = cong₂ f₁ pᵍ pˣ

      -- We compose (p : f₀ g₀ x₀ ≡ f₁ g₀ x₀) on either side with the ajusted paths from above,
      -- over the identification (pᵍ : g₀ ≡ g).  This gives us the desired (non-dependent)
      -- path from (f₀ g x) to (f₁ g x).
      goal : PathP (λ _ → ⟨ Y g ⟩) (f₀ g x) (f₁ g x)
      goal = doubleCompPathP (λ i _ → ⟨ Y (pᵍ i) ⟩) p₀′ p p₁′

    -- Since X is transitive (= ∫ G X is connected), there merely exists a path (g₀ , x₀) ≡ (g , x)
    -- for any g, x.  The goal is a proposition, so we can apply [path-ext-conn] from above:
    path-ext : ∀ g x → f₀ g x ≡ f₁ g x
    path-ext g x = PT.rec (str (Y g) _ _)
      (λ ∫-path → path-ext-conn g x (cong fst ∫-path) (cong snd ∫-path))
      (isPathConnected→merePath is-transitive-X (g₀ , x₀) (g , x))

    path : f₀ ≡ f₁
    path i g x = path-ext g x i

    goal : Path (fiber (ev x₀) y) (f₀ , p₀) (f₁ , p₁)
    goal = Σ≡Prop (λ f → str (Y g₀) _ _) path
