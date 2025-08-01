module GpdCont.HomotopyGroup.Subgroup where

open import GpdCont.Prelude
open import GpdCont.Connectivity
open import GpdCont.Embedding
open import GpdCont.HomotopySet
open import GpdCont.Univalence
import      GpdCont.SetTruncation as ST

open import GpdCont.HomotopyGroup.Base
open import GpdCont.HomotopyGroup.Aut
open import GpdCont.HomotopyGroup.Morphism
open import GpdCont.HomotopyGroup.Action

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Functions.Fibration using (fibrationEquiv)
open import Cubical.Functions.FunExtEquiv using (funExtEquiv)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  variable
    ℓ ℓ′ ℓX : Level

Subgroup : (ℓX : Level) (G : hGroup ℓ) → Type _
Subgroup ℓX G = Σ[ X ∈ hAction ℓX G ] Σ[ x₀ ∈ ⟨ X (hGroup.pt₀ G) ⟩ ] isTransitive G X

isSetSubgroup : ∀ {ℓX} {G : hGroup ℓ} → isSet (Subgroup ℓX G)
isSetSubgroup {G} s₀@(X , x₀ , is-trans-X) s₁@(Y , y₀ , is-trans-Y) = goal where
  private module G = hGroup G
  is-emb-evX : isProp (Σ[ f ∈ (∀ g → ⟨ X g ⟩ → ⟨ Y g ⟩) ] f G.pt₀ x₀ ≡ y₀)
  is-emb-evX = isTransitive→isEmbeddingEv G X Y is-trans-X x₀ y₀

  path-equiv : (s₀ ≡ s₁) ≃ Σ (fiber (ev G X Y x₀) y₀) _
  path-equiv =
    (s₀ ≡ s₁) ≃⟨ invEquiv ΣPathP≃PathPΣ ⟩
    Σ[ p ∈ (X ≡ Y) ] PathP (λ i → Σ _ _) _ _ ≃⟨ Σ-cong-equiv-snd (λ p → invEquiv ΣPathP≃PathPΣ) ⟩
    Σ[ p ∈ (X ≡ Y) ] (PathP (λ i → ⟨ p i G.pt₀ ⟩) x₀ y₀) × PathP (λ i → isTransitive G (p i)) is-trans-X is-trans-Y ≃⟨ Σ-cong-equiv-snd (λ p → Σ-contractSnd $ const (isProp→isContrPathP (λ i → isPropIsTransitive G (p i)) _ _)) ⟩
    Σ[ p ∈ (X ≡ Y) ] (PathP (λ i → ⟨ p i G.pt₀ ⟩) x₀ y₀) ≃⟨ Σ-cong-equiv-fst (invEquiv funExtEquiv) ⟩
    Σ[ p ∈ (∀ g → X g ≡ Y g) ] (PathP (λ i → ⟨ p G.pt₀ i ⟩) x₀ y₀) ≃⟨ Σ-cong-equiv-fst (equivΠCod λ _ → invEquiv hSet≡Equiv) ⟩
    Σ[ p ∈ (∀ g → ⟨ X g ⟩ ≡ ⟨ Y g ⟩) ] (PathP (λ i → p G.pt₀ i) x₀ y₀) ≃⟨ Σ-cong-equiv (equivΠCod λ g → univalence {A = ⟨ X g ⟩} {B = ⟨ Y g ⟩}) (λ p → pathToEquiv (shuffle-snd p)) ⟩
    Σ[ e ∈ (∀ g → ⟨ X g ⟩ ≃ ⟨ Y g ⟩) ] (PathP (λ i → ua (e G.pt₀) i) x₀ y₀) ≃⟨ Σ-cong-equiv-snd (λ e → PathP≃Path _ x₀ y₀) ⟩
    Σ[ e ∈ (∀ g → ⟨ X g ⟩ ≃ ⟨ Y g ⟩) ] (transport (λ i → ua (e G.pt₀) i) x₀ ≡ y₀) ≃⟨ Σ-cong-equiv-snd (λ e → compPathlEquiv $ sym (uaβ (e _) x₀)) ⟩
    Σ[ e ∈ (∀ g → ⟨ X g ⟩ ≃ ⟨ Y g ⟩) ] (equivFun (e G.pt₀) x₀ ≡ y₀) ≃⟨ {! !} ⟩
    Σ[ (f , _) ∈ Σ[ f ∈ (∀ g → ⟨ X g ⟩ → ⟨ Y g ⟩) ] (f G.pt₀ x₀ ≡ y₀) ] (∀ g → isEquiv (f g)) ≃⟨⟩
    Σ[ (f , _) ∈ fiber (ev G X Y x₀) y₀ ] (∀ g → isEquiv (f g)) ≃∎
    where
      shuffle-fst : (X ≡ Y) ≃ (∀ g → ⟨ X g ⟩ ≃ ⟨ Y g ⟩)
      shuffle-fst =
        (X ≡ Y) ≃⟨ invEquiv funExtEquiv ⟩
        (∀ g → X g ≡ Y g) ≃⟨ equivΠCod (λ g → invEquiv hSet≡Equiv ∙ₑ univalence) ⟩
        (∀ g → ⟨ X g ⟩ ≃ ⟨ Y g ⟩) ≃∎

      shuffle-snd : (p : ∀ g → ⟨ X g ⟩ ≡ ⟨ Y g ⟩) → PathP (λ i → p G.pt₀ i) x₀ y₀ ≡ PathP (λ i → ua (pathToEquiv (p G.pt₀)) i) x₀ y₀
      shuffle-snd p = λ j → PathP (λ i → uaη (p G.pt₀) (~ j) i) x₀ y₀

  path-embed : (s₀ ≡ s₁) ↪ fiber (ev G X Y x₀) y₀
  path-embed = compEmbedding
    (EmbeddingΣProp (λ (f , _) → isPropΠ λ g → isPropIsEquiv (f g)))
    (Equiv→Embedding path-equiv)

  goal : isProp (s₀ ≡ s₁)
  goal = Embedding-into-hLevel→hLevel 0 path-embed is-emb-evX

Subgroup→hGroup : {G : hGroup ℓ} → Subgroup ℓX G → hGroup (ℓ-max ℓ ℓX)
Subgroup→hGroup {G} (X , x₀ , is-transitive-X) = pointedConnectedGroupoid→hGroup ⟨ ∫ G X ⟩ pt is-conn (str $ ∫ G X) where
  module G = hGroup G

  pt : ⟨ ∫ G X ⟩
  pt .fst = G.pt₀
  pt .snd = x₀

  is-conn : isPathConnected ⟨ ∫ G X ⟩
  is-conn = is-transitive-X

open hGroupHom using (fun)

isMono : (G : hGroup ℓ) (H : hGroup ℓ′) (φ : hGroupHom G H) → Type _
isMono G H φ = isOfHLevelFun 2 (φ .fun)

isSetFiberPt→isMono : (G : hGroup ℓ) (H : hGroup ℓ′)
  → (φ : hGroupHom G H)
  → isSet (fiber (φ .fun) (hGroup.pt₀ H))
  → isMono G H φ
isSetFiberPt→isMono G H φ = hGroup.elimProp H λ g → isPropIsOfHLevel {A = fiber (φ .fun) g} 2

record hGroupMono (G : hGroup ℓ) (H : hGroup ℓ′) : Type (ℓ-max ℓ ℓ′) where
  field
    hom : hGroupHom G H
    is-mono : isMono G H hom

  open hGroupHom hom public

open hGroupMono

idHGroupMono : (G : hGroup ℓ) → hGroupMono G G
idHGroupMono G .hom = idHGroupHom G
idHGroupMono G .is-mono = isOfHLevelFunId 2

compHGroupMono : ∀ {ℓ″} {G : hGroup ℓ} {H : hGroup ℓ′} {K : hGroup ℓ″}
  → hGroupMono G H
  → hGroupMono H K
  → hGroupMono G K
compHGroupMono φ ψ .hom = (φ .hom) ∙ᴳ (ψ .hom)
compHGroupMono φ ψ .is-mono = isOfHLevelFunComp 2 (ψ .fun) (φ .fun) (ψ .is-mono) (φ .is-mono)

Mono : (ℓ : Level) (H : hGroup ℓ′) → Type _
Mono ℓ H = Σ[ G ∈ hGroup ℓ ] hGroupMono G H

Emb : (ℓ : Level) (H : hGroup ℓ′) → Type _
Emb ℓ H = Σ[ E ∈ Type ℓ ] Σ[ p ∈ (E → ⟨ H ⟩ᵗ) ] isOfHLevelFun 1 p

Emb→Mono : ∀ {ℓ} (H : hGroup ℓ′) → Emb ℓ H → Mono ℓ H
Emb→Mono {ℓ} H (E , p , emb-p) = G , {! !} where
  module H = hGroup H

  e : E
  e = {! fiber p H.pt₀ !}

  G' : Type _
  G' = Σ[ h ∈ ⟨ H ⟩ᵗ ] fiber p h

  G : hGroup ℓ
  G = pointedConnectedGroupoid→hGroup E {! !} {! !} {! !}

MonoEquiv : (H : hGroup ℓ) → Mono ℓ H ≃ (⟨ H ⟩ᵗ → hProp ℓ)
MonoEquiv {ℓ} H =
  {! !} ≃⟨ {! !} ⟩
  Emb ℓ H ≃⟨ invEquiv Σ-assoc-≃ ⟩
  (Σ[ (E , p) ∈ Σ[ E ∈ Type ℓ ] (E → ⟨ H ⟩ᵗ) ] isOfHLevelFun 1 p) ≃⟨ Σ-cong-equiv-fst (fibrationEquiv ⟨ H ⟩ᵗ ℓ) ⟩
  (Σ[ P ∈ (⟨ H ⟩ᵗ → Type ℓ) ] ∀ h → isProp (P h)) ≃⟨ invEquiv Σ-Π-≃ ⟩
  (⟨ H ⟩ᵗ → Σ[ P ∈ Type ℓ ] isProp P) ≃∎
  -- (Σ[ G ∈ hGroup ℓ ] Σ[ ι ∈ hGroupHom G H ] isMono G H ι) ≃⟨ {! !} ⟩
  -- (Σ[ (E , p) ∈ Σ[ E ∈ Type (ℓ-suc ℓ) ] (E → hGroup ℓ) ] isOfHLevelFun 1 p) ≃⟨ Σ-cong-equiv-fst (fibrationEquiv (hGroup ℓ) ℓ) ⟩
  -- (Σ[ P ∈ (hGroup ℓ → Type (ℓ-suc ℓ)) ] ∀ G → isProp (P G)) ≃⟨ invEquiv Σ-Π-≃ ⟩
  -- (hGroup ℓ → Σ[ P ∈ Type (ℓ-suc ℓ) ] isProp P) ≃∎

isSetMono : ∀ {ℓ} {H : hGroup ℓ′} → isSet (Mono ℓ H)
isSetMono {H} = ? -- sub₀@(G₀ , ι₀ , is-mono-ι₀) sub₁@(G₁ , ι₁ , is-mono-ι₁) = {! !} where
  -- path-equiv : {! !} ≃ (sub₀ ≡ sub₁)
  -- path-equiv =
  --   {! !} ≃⟨ {! !} ⟩
  --   Σ[ G ∈ G₀ ≡ G₁ ] Σ[ ι ∈ PathP (λ i → hGroupHom (G i) H) ι₀ ι₁ ] PathP (λ i → isMono (G i) H (ι i)) is-mono-ι₀ is-mono-ι₁ ≃⟨ {! !} ⟩
  --   Σ[ G ∈ G₀ ≡ G₁ ] PathP (λ i → Σ[ ι ∈ hGroupHom (G i) H ] isMono (G i) H ι) (ι₀ , is-mono-ι₀) (ι₁ , is-mono-ι₁) ≃⟨ {! !} ⟩
  --   (sub₀ ≡ sub₁) ≃∎

monoIntoTrivial→isTrivial : (G : hGroup ℓ) (H : hGroup ℓ′)
  → (f : ⟨ G ⟩ᵗ → ⟨ H ⟩ᵗ)
  → isOfHLevelFun 2 f
  → isTrivial H
  → isTrivial G
monoIntoTrivial→isTrivial G H f f-mono is-triv-H = isSet→isTrivial G is-set-G where
  -- The fibers of f are, at the same time:
  --  1) equivalent to all of G
  --  2) sets
  -- Therefore G must me a set, which in turn means that it is trivial.
  fiber-equiv : ∀ h → fiber f h ≃ ⟨ G ⟩ᵗ
  fiber-equiv h = Σ-contractSnd (λ g → isOfHLevelPath 0 is-triv-H (f g) h)

  is-set-G : isSet ⟨ G ⟩ᵗ
  is-set-G = isOfHLevelRespectEquiv 2 (fiber-equiv $ hGroup.pt₀ H) (f-mono _)

isTrivial→isTrivialMono : (H : hGroup ℓ′)
  → isTrivial H
  → ((G , _) : Mono ℓ H)
  → isTrivial G
isTrivial→isTrivialMono H is-triv-H (G , ι) = monoIntoTrivial→isTrivial G H (ι .fun) (ι .is-mono) is-triv-H

aut-map-mono : (A : hGroupoid ℓ) {a₀ : ⟨ A ⟩} (B : hGroupoid ℓ′) {b₀ : ⟨ B ⟩}
  → (f : ⟨ A ⟩ → ⟨ B ⟩)
  → (pres-pt : f a₀ ≡ b₀)
  → isSet (fiber f b₀)
  → hGroupMono (Aut A a₀) (Aut B b₀)
aut-map-mono A {a₀} B {b₀} f pres-pt is-set-fib .hom = aut-map A B f pres-pt
aut-map-mono A {a₀} B {b₀} f pres-pt is-set-fib .is-mono = isTruncFiberPt→isTruncAutMap 1 A B f pres-pt is-set-fib
