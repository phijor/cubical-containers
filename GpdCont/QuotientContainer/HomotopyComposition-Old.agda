{-# OPTIONS --no-require-unique-meta-solutions #-}
open import GpdCont.Prelude

module GpdCont.QuotientContainer.HomotopyComposition (ℓ : Level) where

open import GpdCont.HomotopySet
open import GpdCont.HomotopyGroup.Base
open import GpdCont.HomotopyGroup.Action
open import GpdCont.HomotopyGroup.Subgroup hiding (Emb)
open import GpdCont.HomotopyGroup.Subaction
open import GpdCont.HomotopyGroup.Pi
open import GpdCont.HomotopyGroup.Stabilizer
open import GpdCont.HomotopyGroup.Wreath
open import GpdCont.HomotopyGroup.Morphism
open import GpdCont.HomotopyGroup.Equiv
import      GpdCont.SetTruncation as ST
open import GpdCont.PropositionalTruncation as PT using (_>>=_ ; return)
open import GpdCont.Embedding

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Functions.Logic using (⊤)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)


module Compose
  (S T : Type ℓ)
  (is-set-S : isSet S)
  (is-set-T : isSet T)
  (G : S → hGroup ℓ)
  (H : T → hGroup ℓ)
  (P : (s : S) → hAction ℓ (G s))
  (Q : (t : T) → hAction ℓ (H t))
  where

  private
    module G {s} = hGroup (G s)

  Uᴰ : (s : S) → Type _
  Uᴰ s = ∥ ⟨ ∫ (G s) (precompAction (G s) (P s) (T , is-set-T)) ⟩ ∥₂

  U : Type ℓ
  U = Σ[ s ∈ S ] Uᴰ s

  is-set-U : isSet U
  is-set-U = isSetΣ is-set-S (λ s → ST.isSetSetTrunc)

  -- The shapes of the composite are a sum of orbits of a G-action:
  _ : U ≡ (Σ[ s ∈ S ] ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂)
  _ = refl

  -- The subset of positions in ⟨ P s G.pt₀ ⟩ that f maps to some t:
  module _ {s : S} (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) (t : T) where
    Fixed : ℙ ⟨ P s G.pt₀ ⟩
    Fixed p .fst = ∃[ α ∈ G.pt₀ ≡ g ] f (subst (λ - → ⟨ P s - ⟩) α p) ≡ t
    Fixed p .snd = isProp∃ _ _

    -- Fixed' : {! !}

  -- G acts naturally on the subsets of P.  The stabilizer of the above subsets gives a subaction of this action.
  P* : (s : S) → hAction (ℓ-suc ℓ) (G s)
  P* s = ℙ* (G s) (P s)

  K-sub* : (t : T) (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) → Subaction (ℓ-suc ℓ) (ℓ-suc ℓ) (G s) (P* s)
  K-sub* t s g f = StabℙSubaction (G s) (P s) $ Fixed g f t

  -- Subactions form a set, so this is well-defined for any shape in U:
  K-sub : (t : T) (s : S) → Uᴰ s → Subaction (ℓ-suc ℓ) (ℓ-suc ℓ) (G s) (P* s)
  K-sub t s = ST.rec (isSetSubaction (G s) (P* s)) $ uncurry $ K-sub* t s

  EnvGroupᴰ : S → T → hGroup (ℓ-suc ℓ)
  EnvGroupᴰ s t = (G s) ≀[ P* s ] (H t)

  EnvGroup : S → hGroup (ℓ-suc ℓ)
  EnvGroup s = ΠGroup T (EnvGroupᴰ s)

  envActionᴰ : (s : S) → (t : T) → hAction _ (EnvGroupᴰ s t)
  envActionᴰ s t = WrAction (G s) (P* s) (H t) (Q t)

  envAction : (s : S) → hAction _ (EnvGroup s)
  envAction s = ΠActionΠ (EnvGroupᴰ s) (envActionᴰ s)

  Env : S → Σ[ E ∈ hGroup (ℓ-suc ℓ) ] hAction (ℓ-suc ℓ) E
  Env s = (EnvGroup s , envAction s)

  module Env (s : S) where
    module ᴰ (t : T) where
      Eᴰ : hGroup _
      Eᴰ = (G s) ≀[ P s ] (H t)

      Eᴰ' : hGroup _
      Eᴰ' = (G s) ≀[ P* s ] (H t)

      Wᴰ : hAction _ Eᴰ
      Wᴰ = WrAction (G s) (P s) (H t) (Q t)

      Wᴰ' : hAction _ Eᴰ'
      Wᴰ' = WrAction (G s) (P* s) (H t) (Q t)

    open ᴰ

    E : hGroup _
    E = ΠGroup T Eᴰ

    E' : hGroup _
    E' = ΠGroup T Eᴰ'

    -- TODO: Use ΠActionΣ, then embed into this
    W : hAction _ E
    W = ΠActionΠ Eᴰ Wᴰ

    W' : hAction _ E'
    W' = ΠActionΣ (T , is-set-T) Eᴰ' Wᴰ'

    -- Wᵉ : hAction _ E'
    -- Wᵉ (g , η) = ΣSet (P s {! !}) {! !}

    _ : ∀ e → ⟨ W' e ⟩ ≡ (Σ[ t ∈ T ] Σ[ p? ∈ ℙ ⟨ P s (e .fst t .fst) ⟩ ] ⟨ Q t (e .fst t .snd .fst p?) ⟩)
    _ = λ e → refl

  -- module Test (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) where
  --   Gˢ : hGroup _
  --   Gˢ = Stab' (G s) (λ g → P s g →Set (T , is-set-T)) g f

  module Emb (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) where
    Gˢ : T → hGroup _
    Gˢ t = Stabℙ (G s) (P s) (Fixed g f t)

    Fixed' : T → ℙ ⟨ P s g ⟩
    Fixed' t g .fst = f g ≡ t
    Fixed' t g .snd = is-set-T _ _

    Gˢ' : T → hGroup _
    Gˢ' t = Stabℙ' (G s) (P s) {g₀ = g} (Fixed' t)

    Gˢ↪G : T → Mono _ (G s)
    Gˢ↪G t = StabℙMono (G s) (P s) (Fixed g f t)

    Gˢ'↪G : g ≡ G.pt₀ → T → Mono _ (G s)
    Gˢ'↪G p t = StabℙMono' (G s) (P s) (Fixed' t) p

    Gˢ→G : (t : T) → ⟨ Gˢ t ⟩ᵗ → ⟨ G s ⟩ᵗ
    Gˢ→G t = Gˢ↪G t .snd .fst .fst

    Gˢ-inh-action : (t : T) → (g : ⟨ Gˢ t ⟩ᵗ) → ℙ ⟨ P s (Gˢ→G t g) ⟩
    Gˢ-inh-action t = inhStabℙAction (G s) (P s) (Fixed g f t)

    module _ (t : T) where
      open Env.ᴰ s t public

      X-alt : hAction _ (Gˢ t)
      X-alt = StabℙAction-alt (G s) (P s) (Fixed g f t)

      X : hAction _ (Gˢ t)
      X = StabℙAction (G s) (P s) (Fixed g f t)

      X' : hAction _ (Gˢ' t)
      X' = StabℙAction-alt' (G s) (P s) (Fixed' t)

      Kᴰ : hGroup _
      Kᴰ = (Gˢ t) ≀[ X ] (H t)

      Kᴰ-alt : hGroup _
      Kᴰ-alt = (Gˢ t) ≀[ X-alt ] (H t)

      _ : ⟨ Kᴰ ⟩ᵗ ≡ ⟨ (Gˢ t) ≀[ P* s ∘ Gˢ→G t ] (H t) ⟩ᵗ
      _ = refl

      -- Latest attempt
      Kᴰ-canonical : hGroup _
      Kᴰ-canonical = (Gˢ' t) ≀[ X' ] (H t)

      _ : ⟨ Kᴰ-canonical ⟩ᵗ ≡ ⟨ (Gˢ' t) ≀[ (λ ((g , p?) , _) → (Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ p? p ⟩) , _) ] (H t) ⟩ᵗ
      _ = refl


      foo : Subaction _ _ (G s) (P s)
      foo = StabℙSubaction-canon (G s) (P s) (Fixed g f t)

      foo' : Subaction _ _ (G s) (P s)
      foo' = StabℙSubaction-canon' (G s) (P s) (Fixed' t) {! !}

      -- TODO: This only seems to work when we already know that f p ≡ t
      frob : Subaction _ _ Eᴰ Wᴰ
      frob .fst .fst = (Gˢ' t) ≀[ X' ] (H t)
      frob .fst .snd .fst = mkHGroupHom ((Gˢ' t) ≀[ X' ] H t) (G s ≀[ P s ] H t) ι (ΣPathP ({! !} , {! !})) where
        ι : ⟨ (Gˢ' t) ≀[ X' ] H t ⟩ᵗ → ⟨ G s ≀[ P s ] H t ⟩ᵗ
        ι (((g' , p?) , gp?-conn) , η , η-conn) .fst = g'
        ι (((g' , p?) , gp?-conn) , η , η-conn) .snd .fst p' = η (p' , ST.pathSetTrunc→recProp (str (p? p')) {! !} gp?-conn) where
          lemmaer :
            ∀ (g' : ⟨ G s ⟩ᵗ)
            → (g-path : g ≡ g')
            → (p' : ⟨ P s g' ⟩)
            → (p? : ℙ ⟨ P s g' ⟩)
            → (Fixed≡ : PathP (λ i → ℙ ⟨ P s (g-path i) ⟩) (Fixed' t) p?) → ⟨ p? p' ⟩
          lemmaer g' = J (λ g' g-path → (p' : ⟨ P s g' ⟩) → (p? : ℙ ⟨ P s g' ⟩) → (Fixed≡ : PathP (λ i → ℙ ⟨ P s (g-path i) ⟩) (Fixed' t) p?) → ⟨ p? p' ⟩)
            (λ p p? Fixed≡ → transport (λ i → ⟨ Fixed≡ i p ⟩) $ the (f p ≡ t) {! !})
          
        ι (((g' , p?) , gp?-conn) , η , η-conn) .snd .snd = {! !}
        
      frob .fst .snd .snd = {! !}
      frob .snd = {! !}

      bar : Subaction _ _ Eᴰ Wᴰ
      bar .fst .fst = Kᴰ-alt
      bar .fst .snd .fst = mkHGroupHom ((Gˢ t) ≀[ X-alt ] H t) (G s ≀[ P s ] H t) ι {! !} where
        ι : ⟨ (Gˢ t) ≀[ X-alt ] H t ⟩ᵗ → ⟨ G s ≀[ P s ] H t ⟩ᵗ
        ι (gˢ , _) .fst = Gˢ→G t gˢ
        ι (((g' , p?) , gp?-conn) , η , η-conn) .snd .fst = η ∘ λ p → p , ST.pathSetTrunc→recProp (str (p? p)) (λ pp → lemma p (cong fst pp) (cong snd pp)) gp?-conn where
          lemma : (p' : ⟨ P s g' ⟩) → (g-path : g' ≡ G.pt₀) (Fixed≡ : PathP (λ i → ℙ ⟨ P s (g-path i) ⟩) p? (Fixed g f t)) → ⟨ p? p' ⟩
          lemma p' g-path Fixed≡ = transport (λ i → ⟨ Fixed≡ (~ i) (transport-filler (cong (λ - → ⟨ P s - ⟩) g-path) p' (~ i)) ⟩) do
            xx ← G.mere-path g
            return (xx , {! !})
            -- (∃-intro {!g-path !} {! !})
          lemmaer :
            ∀ (g' : ⟨ G s ⟩ᵗ)
            → (p? : ℙ ⟨ P s g' ⟩)
            → (p' : ⟨ P s g' ⟩)
            → (g-path : g' ≡ G.pt₀) (Fixed≡ : PathP (λ i → ℙ ⟨ P s (g-path i) ⟩) p? (Fixed g f t)) → ⟨ p? p' ⟩
          lemmaer = G.elimProp {! !} λ where
            p? p' loop loopᴰ → transport (λ i → ⟨ loopᴰ (~ i) (transport-filler (cong (λ - → ⟨ P s - ⟩) loop) p' (~ i)) ⟩) $ ∃-intro {! !} {! !}

        ι (gˢ , η , η-conn) .snd .snd = {! !}

      bar .fst .snd .snd = {! !}
      bar .snd = {! !}

      Rᴰ : hAction _ Kᴰ
      Rᴰ = WrAction (Gˢ t) X (H t) (Q t)

      -- Rᴰ-β : (k@(((g , P?) , gP?-conn) , (η , _)) : ⟨ Kᴰ ⟩ᵗ) → ⟨ Rᴰ k ⟩ ≡ (Σ[ p⊂ ∈ Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ P? p ⟩ ] ⟨ Q t (η p⊂) ⟩)
      -- Rᴰ-β k = refl
      Rᴰ-β : (k@(((g , _) , gP?-conn) , (η , _)) : ⟨ Kᴰ ⟩ᵗ) → ⟨ Rᴰ k ⟩ ≡ (Σ[ p? ∈ ℙ ⟨ P s g ⟩ ] ⟨ Q t (η p?) ⟩)
      Rᴰ-β k = refl

      Rᴰ-alt : hAction _ Kᴰ-alt
      Rᴰ-alt = WrAction (Gˢ t) X-alt (H t) (Q t)

      Rᴰ-alt-β : (k@(((g , P?) , gP?-conn) , (η , _)) : ⟨ Kᴰ-alt ⟩ᵗ) → let x = {! gP?-conn !} in ⟨ Rᴰ-alt k ⟩ ≡ (Σ[ p⊂ ∈ Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ P? p ⟩ ] ⟨ Q t (η p⊂) ⟩)
      Rᴰ-alt-β k = refl

      Kᴰ↪Eᴰ : Mono _ Eᴰ
      Kᴰ↪Eᴰ = WrMono (G s) (P s) (H t) (Gˢ↪G t)

      Kᴰ↪Eᴰ' : Mono _ Eᴰ'
      Kᴰ↪Eᴰ' = WrMono (G s) (P* s) (H t) (Gˢ↪G t)

      {-
      Kιᴰ : hGroup (ℓ-suc ℓ)
      Kιᴰ = Kᴰ↪Eᴰ .fst

      Rᴰ⊂Wᴰ : Subactionᴰ (Gˢ t ≀[ P s ∘ (Gˢ→G t) ] (H t)) Eᴰ (Kᴰ↪Eᴰ .snd .fst) ℓ Wᴰ
      Rᴰ⊂Wᴰ .fst = action where
        action : hAction _ (Gˢ t ≀[ P s ∘ (Gˢ→G t) ] (H t))
        action (((g , P?) , _) , (η , _))= ΣSet (P s g) λ p → Q t (η p)
      Rᴰ⊂Wᴰ .snd = embedding where
        embedding : ((((g , P?) , _) , (η , _)) : ⟨ Gˢ t ≀[ P s ∘ Gˢ→G t ] H t ⟩ᵗ) → (Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ Q t (η p) ⟩) ↪ (Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ Q t (η p) ⟩)
        embedding _ = id↪ _

      Rᴰ↪ : Subaction _ ℓ Eᴰ Wᴰ
      Rᴰ↪ .fst = Kᴰ↪Eᴰ
      Rᴰ↪ .snd = Rᴰ⊂Wᴰ
      -}

    open Env s using (E ; E' ; W ; W')

    K : hGroup _
    K = ΠGroup T Kᴰ

    R : hAction _ K
    R (k , _) = ΠSet λ (t : T) → Rᴰ t (k t)

    K-projr : (t : T) → hGroupHom K (H t)
    K-projr t = compGroupHom K (Kᴰ t) (H t)
      -- Project onto the tᵗʰ component of the product (a wreath product):
      (proj Kᴰ t)
      -- Project out the second component:
      (Wr-projr (Gˢ t) (X t) (H t) (Gˢ-inh-action t))

    K→H : (t : T) → ⟨ K ⟩ᵗ → ⟨ H t ⟩ᵗ
    K→H t = K-projr t .fst

    -- K→H : (p : ⟨ P s g ⟩) → ⟨ K ⟩ᵗ → ⟨ H (f p) ⟩ᵗ
    -- K→H p (k , k-conn) = η p? where
    --   g⋉h : ⟨ (Gˢ (f p)) ≀[ X (f p) ] (H (f p)) ⟩ᵗ
    --   g⋉h = k (f p)

    --   gˢ : ⟨ Gˢ (f p) ⟩ᵗ
    --   gˢ = g⋉h .fst

    --   p? : ℙ ⟨ P s (Gˢ→G _ gˢ) ⟩
    --   p? = g⋉h .fst .fst .snd

    --   η : ⟨ X (f p) gˢ ⟩ → ⟨ H (f p) ⟩ᵗ
    --   η = g⋉h .snd .fst
      

    Rˢ : hAction _ K
    Rˢ k = ΣSet (P s g) λ p → Q (f p) (K→H (f p) k)

    R-test : hAction _ (ΠGroup T Kᴰ-canonical)
    R-test (k , k-conn) .fst = Σ[ t ∈ T ] {! !}
    R-test (k , k-conn) .snd = {! !}

    -- R-canonical (k , k-conn) = {! !}
    R-canonical : hAction _ (ΠGroup T Kᴰ-canonical)
    -- R-canonical (k , k-conn) = {! !}
    R-canonical (k , k-conn) = ΣSet (P s g) λ p → Q (f p) (h p) where module _ (p : ⟨ P s g ⟩) where
      t = f p

      g' : ⟨ G s ⟩ᵗ
      g' = k t .fst .fst .fst

      x' : Σ[ p ∈ ⟨ P s g' ⟩ ] ⟨ k t .fst .fst .snd p ⟩ -- ⟨ X' t (k t .fst) ⟩
      x' = {! k t .fst .snd !}

      h : ⟨ H t ⟩ᵗ
      h = k t .snd .fst x'

    -- R-β : (k : (t : T) → Σ[ gˢ ∈ ⟨ Gˢ t ⟩ᵗ ] ⟨ FunGroup ⟨ X t gˢ ⟩ (H t) ⟩ᵗ)
    --   → (k-conn : _)
    --   → ⟨ R (k , k-conn) ⟩ ≡ ((t : T) → let (((g , P?) , gP?-conn) , (η , _)) = k t in (Σ[ p⊂ ∈ Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ P? p ⟩ ] ⟨ Q t (η p⊂) ⟩))
    -- R-β k _ = refl

    Emb* : Subaction _ _ E W
    Emb* .fst = ΠMono T Eᴰ Kᴰ↪Eᴰ
    Emb* .snd .fst = action where
      action : hAction _ (ΠGroup T (λ t → Gˢ t ≀[ P s ∘ (Gˢ→G t) ] (H t)))
      action k = W (ΠMono T Eᴰ Kᴰ↪Eᴰ .snd .fst .fst k)
    Emb* .snd .snd = embedding where
      embedding : (k : ⟨ ΠGroup T (λ t → Gˢ t ≀[ P s ∘ (Gˢ→G t) ] (H t)) ⟩ᵗ) → ⟨ W (ΠMono T Eᴰ Kᴰ↪Eᴰ .snd .fst .fst k) ⟩ ↪ ⟨ W (ΠMono T Eᴰ Kᴰ↪Eᴰ .snd .fst .fst k) ⟩
      embedding _ = id↪ _

    Emb*-canonical : Subaction _ _ E W
    Emb*-canonical .fst .fst = ΠGroup T Kᴰ-canonical
    Emb*-canonical .fst .snd = {! !}
    Emb*-canonical .snd .fst = R-canonical
    Emb*-canonical .snd .snd = {! !}

    Emb*' : Subaction _ _ E' W'
    Emb*' = (K , K↪E) , (Rˢ , Rˢ⊂W') where
      _ : ⟨ ΠMono T Eᴰ' Kᴰ↪Eᴰ' .fst ⟩ᵗ ≡ ⟨ K ⟩ᵗ
      _ = refl

      K↪E : Σ[ ι ∈ hGroupHom K E' ] (isMono K E' ι)
      K↪E = ΠMono T Eᴰ' Kᴰ↪Eᴰ' .snd

      help : (k : (t : T) → ⟨ Kᴰ t ⟩ᵗ) → (p : ⟨ P s g ⟩) → Σ[ t ∈ T ] ℙ ⟨ P s (k t .fst .fst .fst) ⟩
      help k p = f p , k (f p) .fst .fst .snd

      help-fiber : (k : (t : T) → ⟨ Kᴰ t ⟩ᵗ)
        → (t : T)
        → (p? : ℙ ⟨ P s (k t .fst .fst .fst) ⟩)
        → fiber (help k) (t , p?) ≃ {! !}
      help-fiber k t p? =
        Σ[ p ∈ ⟨ P s g ⟩ ] (f p , k (f p) .fst .fst .snd) ≡ (t , p?)
          ≃⟨ {! !} ⟩
        Σ[ p ∈ ⟨ P s g ⟩ ] Σ[ z ∈ f p ≡ t ] PathP (λ i → ℙ ⟨ P s (k (z i) .fst .fst .fst) ⟩) (k (f p) .fst .fst .snd) p?
          ≃⟨ Σ-cong-equiv-snd (λ p → Σ-contractSnd λ z → isOfHLevelPathP' 0 {! isSetℙ !} {! !} {! !}) ⟩
        Σ[ p ∈ ⟨ P s g ⟩ ] f p ≡ t
          ≃⟨ {! !} ⟩
        {! !}
          ≃∎

      Σhelp : (k : ⟨ K ⟩ᵗ) → ⟨ Rˢ k ⟩ ↪ (Σ[ (t , p?) ∈ Σ[ t ∈ T ] ℙ ⟨ P s (k .fst t .fst .fst .fst) ⟩ ] ⟨ Q t (k .fst t .snd .fst p?) ⟩)
      Σhelp k = Σ-embed-fst λ where
        .fst → help (k .fst)
        .snd → injEmbedding {! !} {! !} -- λ {p₀} {p₁} htpy → {! !}

      Rˢ→W' : ∀ k → ⟨ Rˢ k ⟩ → ⟨ W' (K↪E .fst .fst k) ⟩
      Rˢ→W' (k , k-conn) (p , q) = t , goal where
        t = f p

        g⋉h : ⟨ (Gˢ t) ≀[ P* s ∘ Gˢ→G t ] (H t) ⟩ᵗ
        g⋉h = k t

        g' : ⟨ G s ⟩ᵗ
        g' = g⋉h .fst .fst .fst

        η : ℙ ⟨ P s g' ⟩ → ⟨ H t ⟩ᵗ
        η = g⋉h .snd .fst

        goal : Σ[ p? ∈ ℙ ⟨ P s g' ⟩ ] ⟨ Q t (η p?) ⟩
        goal .fst = g⋉h .fst .fst .snd
        goal .snd = q

      private
        module K = hGroup K

      Rˢ⊂W' : ∀ k → ⟨ Rˢ k ⟩ ↪ ⟨ W' (K↪E .fst .fst k) ⟩
      Rˢ⊂W' k .fst = Rˢ→W' k
      Rˢ⊂W' k .snd = hGroup.elimProp K {P = λ k → isEmbedding (Rˢ→W' k)} (λ _ → isPropIsEmbedding) goal k where -- {! ST.pathSetTrunc→merePath k-conn!} where
        goal : isEmbedding (Rˢ→W' K.pt₀)
        goal = injEmbedding {! !} λ where
          {(p₀ , q₀)} {(p₁ , q₁)} htpy → ΣPathP ({! Rˢ→W' K.pt₀ (p₀ , q₀) .snd .fst  !} , {! !})


    -- Emb*' .snd .fst = action where
    --   action : hAction _ {! !}
    --   action k = {! !}
    -- Emb*' .snd .snd = embedding where
    --   embedding : (k : ⟨ ΠGroup T (λ t → Gˢ t ≀[ P s ∘ (Gˢ→G t) ] (H t)) ⟩ᵗ) → {! !} ↪ ⟨ W' {! !} ⟩
    --   embedding _ = id↪ _

  open Emb using (Emb*)

{-
  Emb : ((s , _) : U) → Subaction (ℓ-suc ℓ) ℓ (Env.E s) (Env.W s)
  Emb = uncurry λ s → ST.rec (isSetSubaction (Env.E s) (Env.W s)) $ uncurry (Emb* s)

  K : U → hGroup (ℓ-suc ℓ)
  K u = Emb u .fst .fst

  R : (u : U) → hAction ℓ (K u)
  R u = Emb u .snd .fst

  module Compute (s : S) (g₀ : ⟨ G s ⟩ᵗ) (f : ⟨ P s g₀ ⟩ → T) where
    u : U
    u = (s , ST.∣ g₀ , f ∣₂)

    Kᵝ : ⟨ K u ⟩ᵗ ≡ ⟨ ΠGroup T (λ (t : T) → Stabℙ (G s) (P s) (Fixed g₀ f t) ⋉ λ ((g , _) , _) → FunGroup ⟨ P s g ⟩ (H t)) ⟩ᵗ
    Kᵝ = refl

    Rᵝ : (k*@(k , _) : ⟨ K u ⟩ᵗ) → ⟨ R u k* ⟩ ≡ ((t : T) → Σ (fst (P s (fst (fst (k* .fst t .fst))))) (λ x → fst (Q t (k* .fst t .snd .fst x))))
      -- (Σ[ p ∈ ⟨ P s g₀ ⟩ ] let (((g , P?) , _) , (η , _)) = k (f p) in ⟨ Q (f p) (η {!p!}) ⟩)
    Rᵝ k = refl
-}

{-
  -- From K-sub we extract a subgroup and -action, on which we define a wreath product of groups:
  Kᴰ : U → T → hGroup (ℓ-suc ℓ)
  Kᴰ (s , uᴰ) t = let ((G' , _) , (P' , _)) = K-sub t s uᴰ in G' ≀[ P' ] (H t)

  K : U → hGroup (ℓ-suc ℓ)
  K u = ΠGroup T (Kᴰ u)

  K↪Env : (u : U) → Mono (ℓ-suc ℓ) (Env (u .fst) .fst)
  K↪Env (s , uᴰ) = ST.rec (isSetMono {H = Env s .fst}) (uncurry goal) uᴰ where
    module _ (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) where
      goalᴰ : ∀ t → Mono _ (G s ≀[ P* s ] H t)
      goalᴰ t = WrMonoSingle (G s) (P* s) (H t) ↪G where
        ↪G : Mono _ (G s)
        ↪G = K-sub t s uᴰ .fst

      goal : Mono _ (Env s .fst)
      goal = ΠMono T (λ t → (G s) ≀[ P* s ] (H t)) goalᴰ

  -- For each shape (u : U), we see that (k : K u) acts on a sigma-type given by P and Q.
  -- TODO: The elimination is not well-defined as it is; I believe this is where we have to
  -- restrict ourselves to a strict subuniverse of sets.
  R* : (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) → hAction ℓ (K (s , ST.∣ g , f ∣₂))
  R* s g f k = ΣSet (P s g) λ p → Q (f p) $ get-H p k where
    get-H : (p : ⟨ P s g ⟩) → ⟨ K (s , ST.∣ g , f ∣₂) ⟩ᵗ → ⟨ H (f p) ⟩ᵗ
    get-H p (k , _) = h where
      g⋉h : Σ[ ((g , _) , _) ∈ ⟨ Stabℙ (G s) (P s) (Fixed g f (f p))⟩ᵗ ] Σ (ℙ ⟨ P s g ⟩ → ⟨ H (f p) ⟩ᵗ) _
      g⋉h = k (f p)

      g' : ⟨ G s ⟩ᵗ
      g' = g⋉h .fst .fst .fst

      sub : ℙ ⟨ P s g' ⟩
      sub = g⋉h .fst .fst .snd

      h : ⟨ H (f p) ⟩ᵗ
      h = g⋉h .snd .fst sub

  K↪Envᴰ : (u : U) → Subactionᴰ (K↪Env u .fst) (Env (u .fst) .fst) (K↪Env u .snd .fst) ℓ (Env (u .fst) .snd)
  K↪Envᴰ = uncurry λ s → ST.elim
    (λ uᴰ → isSetSubactionᴰ (K↪Env (s , uᴰ) .fst) (Env s .fst) (K↪Env (s , uᴰ) .snd .fst) ℓ (Env s .snd))
    (uncurry (goal s))
    where module _ (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) where

    ι : ⟨ K (s , ST.∣ g , f ∣₂) ⟩ᵗ → ⟨ ΠGroup T (λ t → (G s) ≀[ P* s ] (H t)) ⟩ᵗ
    ι = K↪Env (s , ST.∣ g , f ∣₂) .snd .fst .fst

    emb : (k : ⟨ K (s , ST.∣ g , f ∣₂) ⟩ᵗ) → ⟨ R* s g f k ⟩ ↪ ⟨ Env s .snd (ι k) ⟩
    emb k .fst = the (Σ ⟨ P s g ⟩ _ → (t : T) → Σ ⟨ ℙ* (G s) (P s) (ι k .fst t .fst) ⟩ _)
      λ { (p , q) t → {!  !} , {! !} }
    emb k .snd = {! !}

    goal : Subactionᴰ (K (s , ST.∣ g , f ∣₂)) (Env s .fst) (K↪Env (s , ST.∣ g , f ∣₂) .snd .fst) ℓ (Env s .snd)
    goal .fst = R* s g f
    goal .snd = emb

  KR : (u : U) → Subaction (ℓ-suc ℓ) ℓ (Env (u .fst) .fst) (Env (u .fst) .snd)
  KR u .fst = K↪Env u
  KR u .snd = K↪Envᴰ u

  -- KR' : (s : S) → Uᴰ s → Subaction (ℓ-suc ℓ) ℓ (Env s .fst) (Env s .snd)


  R : (u : U) → hAction ℓ (K u)
  -- R = uncurry λ s → ST.elim {! !} $ uncurry (R* s)
  R u = {! K↪Envᴰ u .fst !}

  {-
  R' : (u : U) → hAction ℓ (K u)
  R' = uncurry λ s → ST.elim→Gpd {! !} (λ (g , f) → R* s g f) {! (well-defined s) !} where module _ (s : S) where
    well-defined : (gx₀ gx₁ : Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T)) → (pq₀ pq₁ : gx₀ ≡ gx₁)
      → SquareP
        (λ i j → hAction ℓ (K (s , ST.squash-cong pq₀ pq₁ i j)))
          (λ i → R* s (pq₀ i .fst) (pq₀ i .snd))
          (λ i → R* s (pq₁ i .fst) (pq₁ i .snd))
          (refl′ (R* s (gx₀ .fst) (gx₀ .snd)))
          (refl′ (R* s (gx₁ .fst) (gx₁ .snd)))
    well-defined gx₀ gx₁ pq₀ pq₁ i j k = {!k!}

    well-defined' : (gx₀ gx₁ : Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T)) → (pq₀ pq₁ : gx₀ ≡ gx₁)
      → SquareP
        (λ j i → hAction ℓ (K (s , ST.squash-cong pq₀ pq₁ i j)))
          (refl′ (R* s (gx₀ .fst) (gx₀ .snd)))
          (refl′ (R* s (gx₁ .fst) (gx₁ .snd)))
          (λ i → R* s (pq₀ i .fst) (pq₀ i .snd))
          (λ i → R* s (pq₁ i .fst) (pq₁ i .snd))
    well-defined' gx₀ gx₁ pq₀ pq₁ = {! !}
  -}
  -}

{-
module UnitRight
  (S T : Type ℓ)
  (is-set-S : isSet S)
  (is-set-T : isSet T)
  (G : S → hGroup ℓ)
  (H : T → hGroup ℓ)
  (P : (s : S) → hAction ℓ (G s))
  (Q : (t : T) → hAction ℓ (H t))

  (is-contr-T : isContr T)
  (is-triv-H : ∀ t → isTrivial (H t))
  (is-contr-Q : ∀ t h → isContr ⟨ Q t h ⟩)
  where

  open Compose S T is-set-S is-set-T G H P Q

  private
    module G s = hGroup (G s)
    t₀ = is-contr-T .fst

  is-contr-shapeᴰ : ∀ s → isContr (Uᴰ s)
  is-contr-shapeᴰ s = isOfHLevelRespectEquiv 0 equiv (G.is-connected s) where
    equiv : ∥ ⟨ G s ⟩ᵗ ∥₂ ≃ ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂
    equiv = ST.setTruncEquiv $ invEquiv (Σ-contractSnd λ g → isContrΠ λ _ → is-contr-T)

  shape-unit-right : U ≃ S
  shape-unit-right = Σ-contractSnd is-contr-shapeᴰ

  group-unit-right* : (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) → hGroupEquiv (K (s , ST.∣ g , f ∣₂)) (G s)
  group-unit-right* s g f =
    (ΠGroup T {!Kᴰ !}) ≃ᴳ⟨ {! !} ⟩
    G s ∎ᴳ

    -- ΠGroup T (Kᴰ (s , ST.∣ g , f ∣₂)) ≃ᴳ⟨ ΠGroupContractDomain T (Kᴰ (s , ST.∣ g , f ∣₂)) is-contr-T ⟩
    -- (Stab (G s) (P* s) (Fixed g f t₀) ≀[ StabAction (G s) (P* s) (Fixed g f t₀) ] H t₀) ≃ᴳ⟨ WrContractSnd (Stab (G s) (P* s) (Fixed g f t₀)) (StabAction (G s) (P* s) (Fixed g f t₀)) (H t₀) (is-triv-H t₀) ⟩
    -- (Stabℙ (G s) (P s) (Fixed g f t₀)) ≃ᴳ⟨ StabℙCongEquiv (G s) (P s) (Fixed g f t₀) (λ _ → ⊤) Fixed≡⊤ ⟩
    -- (Stabℙ (G s) (P s) (λ _ → ⊤)) ≃ᴳ⟨ StabℙAllEquiv (G s) (P s) ⟩
    -- (G s) ∎ᴳ
    where
      open Emb s g f

      fix-all : ∀ p → ⟨ Fixed g f t₀ p ⟩
      fix-all p = do
        pt₀≡g ← G.mere-path s g
        return $ pt₀≡g , sym (is-contr-T .snd (f (subst (λ - → ⟨ P s - ⟩) pt₀≡g p)))

      Fixed≡⊤ : ∀ p → ⟨ Fixed g f t₀ p ⟩ ≡ Unit*
      Fixed≡⊤ p = isContr→≡Unit* $ inhProp→isContr (fix-all p) (str (Fixed g f t₀ p))

  -- group-unit-right : ∀ u → hGroupEquiv (K u) (G (u .fst))
  -- group-unit-right = uncurry λ s → ST.elim (λ uᴰ → isSetHGroupEquiv (K (s , uᴰ)) (G s)) (uncurry (group-unit-left* s))

module UnitLeft
  (S T : Type ℓ)
  (is-set-S : isSet S)
  (is-set-T : isSet T)
  (G : S → hGroup ℓ)
  (H : T → hGroup ℓ)
  (P : (s : S) → hAction ℓ (G s))
  (Q : (t : T) → hAction ℓ (H t))

  (is-contr-S : isContr S)
  (is-triv-G : ∀ s → isTrivial (G s))
  (is-contr-P : ∀ s g → isContr ⟨ P s g ⟩)
  where

  open Compose S T is-set-S is-set-T G H P Q
  private
    module G s = hGroup (G s)
    s₀ = is-contr-S .fst

  shape-unit-right' : U ≃ T
  shape-unit-right' =
    Σ[ s ∈ S ] ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂ ≃⟨ Σ-contractFst is-contr-S ⟩
    ∥ Σ[ g ∈ ⟨ G s₀ ⟩ᵗ ] (⟨ P s₀ g ⟩ → T) ∥₂ ≃⟨ ST.setTruncEquiv under-trunc ⟩
    ∥ T ∥₂ ≃⟨ ST.setTruncIdempotent≃ is-set-T ⟩
    T ≃∎
    where
    under-trunc : (Σ[ g ∈ ⟨ G s₀ ⟩ᵗ ] (⟨ P s₀ g ⟩ → T)) ≃ T
    under-trunc =
      (Σ[ g ∈ ⟨ G s₀ ⟩ᵗ ] (⟨ P s₀ g ⟩ → T)) ≃⟨ Σ-contractFst (is-triv-G _) ⟩
      (⟨ P s₀ _ ⟩ → T) ≃⟨ Π-contractDom (is-contr-P s₀ _) ⟩
      T ≃∎

  U→T : U → T
  U→T (s , uᴰ) = ST.rec is-set-T (λ (g , f) → f (is-contr-P s g .fst)) uᴰ

  shape-unit-right-iso : Iso U T
  shape-unit-right-iso .Iso.fun = U→T
  shape-unit-right-iso .Iso.inv t .fst = s₀
  shape-unit-right-iso .Iso.inv t .snd = ST.∣ is-triv-G s₀ .fst , const t ∣₂
  shape-unit-right-iso .Iso.rightInv t = refl
  shape-unit-right-iso .Iso.leftInv = uncurry λ s → ST.elim (λ _ → isOfHLevelPath 2 is-set-U _ _) {! !}
    -- λ where
    -- (g , f) → ΣPathP λ where
    --   .fst → isContr→isProp is-contr-S _ _
    --   .snd i → {! !}

  shape-unit-right : U ≃ T
  shape-unit-right = isoToEquiv shape-unit-right-iso


  _ : ∀ s (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) → equivFun shape-unit-right (s , ST.∣ g , f ∣₂) ≡ f (is-contr-P s g .fst)
  _ = λ s g f → refl

  group-unit-right* : (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) → hGroupEquiv (K (s , ST.∣ g , f ∣₂)) (H (f (is-contr-P s g .fst)))
  group-unit-right* s g f = ?
    ΠGroup T (λ t → StabG t ≀[ StabGAction t ] H t)
      ≃ᴳ⟨ ΠGroupEquivCodomain
        (λ t → StabG t ≀[ StabGAction t ] H t)
        (λ t → FunGroup ⟨ StabGAction t (hGroup.pt₀ (StabG t)) ⟩ (H t))
        (λ t → WrContractFst
          (StabG t)
          (StabGAction t)
          (H t)
          (isTrivialStab (G s) (P* s) (Fixed g f t) (is-triv-G s))
        )
      ⟩
    ΠGroup T (λ t → FunGroup (X t) (H t))
      ≃ᴳ⟨ ΠGroupCurryEquiv {L = X} (λ t → const (H t)) ⟩
    ΠGroup (Σ T X) (λ (t , _) → H t)
      ≃ᴳ⟨ {! !} ⟩
    (H (f (is-contr-P s g .fst))) ∎ᴳ
    where
      StabG : T → hGroup (ℓ-suc ℓ)
      StabG t = Stab (G s) (P* s) (Fixed g f t)

      StabGAction : (t : T) → hAction _ (StabG t)
      StabGAction t = StabAction (G s) (P* s) (Fixed g f t)

      X : T → Type _
      X t = ⟨ StabGAction t (hGroup.pt₀ (StabG t)) ⟩

      ΣTX-equiv : Σ T X ≃ {! !}
      ΣTX-equiv =
        Σ[ t ∈ T ] ⟨ P* s (G.pt₀ s) ⟩ ≃⟨⟩
        Σ[ t ∈ T ] ℙ ⟨ P s (G.pt₀ s) ⟩ ≃⟨ Σ-cong-equiv-snd $ const (Π-contractDom (is-contr-P _ _)) ⟩
        Σ[ t ∈ T ] hProp ℓ ≃⟨ {! !} ⟩
        {! !} ≃∎

      is-contr-ΣTX : isContr (Σ T X)
      is-contr-ΣTX = {! !}
 
  group-unit-right : ∀ u → hGroupEquiv (K u) (H (U→T u))
  group-unit-right = uncurry λ s → ST.elim (λ uᴰ → isSetHGroupEquiv (K (s , uᴰ)) (H (U→T (s , uᴰ)))) (uncurry (group-unit-right* s))
  -}
