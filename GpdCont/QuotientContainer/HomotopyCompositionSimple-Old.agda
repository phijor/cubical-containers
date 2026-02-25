{-# OPTIONS --no-require-unique-meta-solutions #-}
open import GpdCont.Prelude

module GpdCont.QuotientContainer.HomotopyCompositionSimple (ℓ : Level) where

open import GpdCont.HomotopySet
open import GpdCont.HomotopyGroup.Base
open import GpdCont.HomotopyGroup.Action
open import GpdCont.HomotopyGroup.Subgroup hiding (Emb)
open import GpdCont.HomotopyGroup.Subaction
open import GpdCont.HomotopyGroup.Pi
open import GpdCont.HomotopyGroup.Stabilizer
open import GpdCont.HomotopyGroup.Aut
open import GpdCont.HomotopyGroup.Wreath
open import GpdCont.HomotopyGroup.Morphism
open import GpdCont.HomotopyGroup.Equiv
import      GpdCont.SetTruncation as ST
open import GpdCont.PropositionalTruncation as PT using (_>>=_ ; return)
open import GpdCont.Embedding
open import GpdCont.Connectivity

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Functions.Logic using (⊤)
open import Cubical.Functions.Embedding
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

{-
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
    module H {t} = hGroup (H t)

  Sh : Type ℓ
  Sh = Σ[ s ∈ S ] (⟨ ∫ (G s) (P s) ⟩ → T)

  is-set-Sh : isSet Sh
  is-set-Sh = isSetΣ is-set-S λ s → isSetΠ λ _ → is-set-T

  Gr : Sh → hGroup ℓ
  Gr (s , f) = G s ⋉ λ g → ΠGroup ⟨ P s g ⟩ λ p → H (f (g , p))

  Gr' : Sh → hGroup ℓ
  Gr' (s , f) = Aut G' (λ t → ({! !} , {! !}) , {! !}) ⋉ {! !} where
    G' : hGroupoid ℓ
    G' .fst = (t : T) → fiber f t
    G' .snd = {! !}

  Ps : (u : Sh) → hAction ℓ (Gr u)
  Ps (s , f) (g , η , _) = ΣSet (P s g) λ p → Q (f (g , p)) (η p)

  module UnitLeft
    (is-contr-S : isContr S)
    (is-triv-G : ∀ s → isTrivial (G s))
    (is-contr-P : ∀ s g → isContr ⟨ P s g ⟩)
    where
    private
      s₀ = is-contr-S .fst

      g₀ : {s : S} → ⟨ G s ⟩ᵗ
      g₀ {s} = is-triv-G s .fst

      p₀ : {s : S} {g : ⟨ G s ⟩ᵗ} → ⟨ P s g ⟩
      p₀ {s} {g} = is-contr-P s g .fst

      is-contr-∫ : ∀ s → isContr ⟨ ∫ (G s) (P s) ⟩
      is-contr-∫ s = isContrΣ (is-triv-G s) (is-contr-P s)

    Sh-unit-left : Sh ≃ T
    Sh-unit-left =
      Sh ≃⟨ Σ-contractFst is-contr-S ⟩
      (⟨ ∫ (G s₀) (P s₀) ⟩ → T) ≃⟨ Π-contractDom (is-contr-∫ s₀) ⟩
      T ≃∎

    Gr-unit-left : ((s , f) : Sh) → hGroupEquiv (Gr (s , f)) (H (f (g₀ , p₀)))
    Gr-unit-left (s , f) =
      G s ⋉ (λ g → ΠGroup ⟨ P s g ⟩ λ p → H (f (g , p))) ≃ᴳ⟨ hGroupEquiv.inv (ΠGroup ⟨ P s g₀ ⟩ (λ p → H (f (g₀ , p)))) (G s ⋉ (λ g → ΠGroup ⟨ P s g ⟩ λ p → H (f (g , p)))) step-I ⟩
      ΠGroup ⟨ P s g₀ ⟩ (λ p → H (f (g₀ , p))) ≃ᴳ⟨ step-II ⟩
      H (f (g₀ , p₀)) ∎ᴳ

      where
        step-I : ΠGroup ⟨ P s g₀ ⟩ (λ p → H (f (g₀ , p))) ≃ᴳ (G s ⋉ (λ g → ΠGroup ⟨ P s g ⟩ λ p → H (f (g , p))))
        step-I = isContrFst→⋉-contractFst (G s) (λ g → ΠGroup ⟨ P s g ⟩ λ p → H (f (g , p))) (is-triv-G s)

        step-II : ΠGroup ⟨ P s g₀ ⟩ (λ p → H (f (g₀ , p))) ≃ᴳ H (f (g₀ , p₀))
        step-II = ΠGroupContractDomain ⟨ P s g₀ ⟩ (λ p → H (f (g₀ , p))) (is-contr-P s g₀)

    ι : ((s , f) : Sh) → ⟨ Gr (s , f) ⟩ᵗ → ⟨ H (f (g₀ , p₀)) ⟩ᵗ
    ι sh = hGroupEquiv.fun (Gr sh) (H _) (Gr-unit-left sh)

    Ps-unit-left : ((s , f) : Sh) (gr@(g , η , _) : ⟨ Gr (s , f) ⟩ᵗ) → ⟨ Ps (s , f) gr ⟩ ≃ ⟨ Q (f (g , p₀)) (η p₀) ⟩
    Ps-unit-left (s , f) (g , η , η-conn) = Σ-contractFst (is-contr-P s g)
      -- Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ Q (f (g , p)) (η p) ⟩ ≃⟨ Σ-contractFst (is-contr-P s g) ⟩
      -- ⟨ Q (f (g , p₀)) (η p₀) ⟩ ≃⟨ {!substEquiv (λ - → ⟨ Q (f !} ⟩
      -- ⟨ Q (f (g₀ , p₀)) (ι (s , f) (g , η , η-conn)) ⟩ ≃∎

  module UnitRight
    (is-contr-T : isContr T)
    (is-triv-H : ∀ t → isTrivial (H t))
    (is-contr-Q : ∀ t h → isContr ⟨ Q t h ⟩)
    where
    private
      t₀ = is-contr-T .fst

      h₀ : {t : T} → ⟨ H t ⟩ᵗ
      h₀ {t} = is-triv-H t .fst

      q₀ : {t : T} {h : ⟨ H t ⟩ᵗ} → ⟨ Q t h ⟩
      q₀ {t} {h} = is-contr-Q t h .fst

    Sh-unit-right : Sh ≃ S
    Sh-unit-right = Σ-contractSnd λ s → isContrΠ λ _ → is-contr-T

    Gr-unit-right : ((s , f) : Sh) → hGroupEquiv (Gr (s , f)) (G s)
    Gr-unit-right (s , f) = ⋉-contractSnd (G s) (λ g → ΠGroup ⟨ P s g ⟩ λ p → H (f (g , p))) λ where
      g → isContrΠGroup ⟨ P s g ⟩ (λ p → H (f (g , p))) λ p → is-triv-H _

    Ps-unit-right : ((s , f) : Sh) (gr@(g , η , _) : ⟨ Gr (s , f) ⟩ᵗ) → ⟨ Ps (s , f) gr ⟩ ≃ ⟨ P s g ⟩
    Ps-unit-right (s , f) (g , η , _) = Σ-contractSnd λ p → is-contr-Q (f (g , p)) (η p)

module Assoc
  (S T U : Type ℓ)
  (is-set-S : isSet S)
  (is-set-T : isSet T)
  (is-set-U : isSet U)
  (G : S → hGroup ℓ)
  (H : T → hGroup ℓ)
  (K : U → hGroup ℓ)
  (P : (s : S) → hAction ℓ (G s))
  (Q : (t : T) → hAction ℓ (H t))
  (R : (u : U) → hAction ℓ (K u))
  where
    module 𝔽∘𝔾 = Compose S T is-set-S is-set-T G H P Q
    module 𝔾∘𝕂 = Compose T U is-set-T is-set-U H K Q R
    module [𝔽∘𝔾]∘K = Compose
      𝔽∘𝔾.Sh U
      𝔽∘𝔾.is-set-Sh is-set-U
      𝔽∘𝔾.Gr K
      𝔽∘𝔾.Ps R
    module 𝔽∘[𝔾∘K] = Compose
      S 𝔾∘𝕂.Sh
      is-set-S 𝔾∘𝕂.is-set-Sh
      G 𝔾∘𝕂.Gr
      P 𝔾∘𝕂.Ps

    foo : [𝔽∘𝔾]∘K.Sh → 𝔽∘[𝔾∘K].Sh
    foo ((s , f) , e) .fst = s
    foo ((s , f) , e) .snd (g , p) .fst = f (g , p)
    foo ((s , f) , e) .snd (g , p) .snd (h , q) = e ((g , η) , p , {! !}) where
      η : ⟨ ΠGroup ⟨ P s g ⟩ (λ - → H (f (g , -))) ⟩ᵗ
      η .fst p' = subst (λ - → ⟨ H - ⟩ᵗ) {!p' !} h
      η .snd = {! !}

    bar : 𝔽∘[𝔾∘K].Sh → [𝔽∘𝔾]∘K.Sh
    bar (s , e) .fst .fst = s
    bar (s , e) .fst .snd (g , p) = the T $ e (g , p) .fst
    bar (s , e) .snd ((g , η , _) , p , q) = e (g , p) .snd (η p , q)

    Sh-assoc : [𝔽∘𝔾]∘K.Sh ≃ 𝔽∘[𝔾∘K].Sh
    Sh-assoc =
      Σ[ (s , f) ∈ Σ[ s ∈ S ] (⟨ ∫ (G s) (P s) ⟩ → T) ] _ ≃⟨ Σ-assoc-≃ ⟩
      Σ[ s ∈ S ] Σ[ f ∈ (⟨ ∫ (G s) (P s) ⟩ → T) ] (⟨ ∫ (𝔽∘𝔾.Gr (s , f)) (𝔽∘𝔾.Ps (s , f)) ⟩ → U) ≃⟨⟩
      Σ[ s ∈ S ] Σ[ f ∈ (⟨ ∫ (G s) (P s) ⟩ → T) ] ((Σ[ gr ∈ ⟨ 𝔽∘𝔾.Gr (s , f) ⟩ᵗ ] ⟨ 𝔽∘𝔾.Ps (s , f) gr ⟩) → U) ≃⟨⟩
      Σ[ s ∈ S ] Σ[ f ∈ (⟨ ∫ (G s) (P s) ⟩ → T) ] ((Σ[ (g , η , _) ∈ Σ[ g ∈ ⟨ G s ⟩ᵗ ] Σ ((p : ⟨ P s g ⟩) → ⟨ H (f (g , p)) ⟩ᵗ) _ ] Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ Q (f (g , p)) (η p) ⟩) → U) ≃⟨ {! !} ⟩
      {! !} ≃⟨ {! !} ⟩
      Σ[ s ∈ S ] ((Σ[ g ∈ ⟨ G s ⟩ᵗ ] ⟨ P s g ⟩) → Σ[ t ∈ T ] (Σ[ h ∈ ⟨ H t ⟩ᵗ ] ⟨ Q t h ⟩ → U)) ≃∎
-}

module ComposeFix
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
    module H {t} = hGroup (H t)

  Sh : Type ℓ
  Sh = Σ[ s ∈ S ] ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂

  Fib : ∀ {s} → ⟨ G s ⟩ᵗ → hSet (ℓ-suc ℓ)
  Fib {s} g .fst = ℙ ⟨ P s g ⟩
  Fib {s} g .snd = isSetℙ

  Pᴰ : ∀ {s} → (t : T) → ⟨ ∫ (G s) Fib ⟩ → hSet ℓ
  Pᴰ t (g , fix) .fst = Σ[ p ∈ ⟨ P _ g ⟩ ] ⟨ fix p ⟩
  Pᴰ t (g , fix) .snd = isSetΣSndProp (str (P _ g)) (str ∘ fix)

  EnvAct : (s : S) → T → hAction _ (G s)
  EnvAct s t g .fst = Σ[ p ∈ ⟨ P s g ⟩ ] ∀ (f : (⟨ P s g ⟩ → T)) → f p ≡ t
  EnvAct s t g .snd = isSetΣ (str (P s g)) λ p → isSetΠ λ f → isProp→isSet $ is-set-T _ _
  -- EnvAct s t g .fst = Σ[ f ∈ (⟨ P s g ⟩ → T) ] Σ[ p ∈ ⟨ P s g ⟩ ] f p ≡ t
  -- EnvAct s t g .snd = isSetΣ (isSet→ is-set-T) λ f → isSetΣSndProp (str (P s g)) λ p → is-set-T _ _

  env₀ : (s : S) (t : T) → ℙ ⟨ P s G.pt₀ ⟩
  -- env₀ s t p .fst = PT.∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] Σ[ f ∈ (⟨ P s g ⟩ → T) ] Σ[ γ ∈ G.pt₀ ≡ g ] f (subst (λ - → ⟨ P s - ⟩) γ p) ≡ t ∥₁
  env₀ s t p₀ .fst = (g : ⟨ G s ⟩ᵗ) → (f : ⟨ P s g ⟩ → T) → ∃[ γ ∈ G.pt₀ ≡ g ] f (subst (λ - → ⟨ P s - ⟩) γ p₀) ≡ t
  env₀ s t p₀ .snd = {! !}

  Envᴰ : S → T → hGroup ℓ
  Envᴰ s t = G s ≀[ EnvAct s t ] H t
  -- P' : (s : S) (t : T) → hAction _ (G s)
  -- P' s t g = Pᴰ t (g , λ p → Unit* , ?)

  -- Envᴰ : S → T → hGroup ℓ
  -- Envᴰ s t = G s ≀[ P' s t ] H t

  -- Eᴰ : S → T → hGroup ℓ
  -- Eᴰ s t = Aut ΣG (G.pt₀ , refl) where
  --   ΣG : hGroupoid ℓ
  --   ΣG .fst = Σ[ g₀ ∈ ⟨ G s ⟩ᵗ ] g₀ ≡ G.pt₀
  --   ΣG .snd = isGroupoidΣ (G.is-groupoid) λ g₀ → isSet→isGroupoid (G.is-groupoid g₀ _)
  r? : (s : S) (t : T) → (g₀ : ⟨ G s ⟩ᵗ) (p₀ : ⟨ P s g₀ ⟩) → ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂ → hProp ℓ
  r? s t g₀ p₀ = ST.rec isSetHProp λ where
    (g , f) .fst → ∃[ γ ∈ g₀ ≡ g ] f (subst (λ - → ⟨ P s - ⟩) γ p₀) ≡ t
    (g , f) .snd → isProp∃ _ _

  Pʳ : (sh : Sh) (t : T) → hAction ℓ (G (sh .fst))
  Pʳ (s , ∣f∣) t g .fst = Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ r? s t g p ∣f∣ ⟩
  Pʳ (s , ∣f∣) t g .snd = isSetΣSndProp (str (P s g)) λ p → str $ r? s t g p ∣f∣

  -- Eᴰ : (sh : Sh) → T → hGroup _
  -- Eᴰ sh t = G (sh .fst) ≀[ Pʳ sh t ] H t

  Eᴰ : (sh : Sh) → T → hGroup _
  Eᴰ (s , ∣f∣) t = Stabℙ (G s) (P s) p? ≀[ StabℙAction-alt (G s) (P s) p? ] H t module Eᴰ where
    fix₀ : ⟨ P s G.pt₀ ⟩ → Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) → hProp ℓ
    fix₀ p₀ (g , f) .fst = ∃[ γ ∈ G.pt₀ ≡ g ] f (subst (λ - → ⟨ P s - ⟩) γ p₀) ≡ t
    fix₀ p₀ (g , f) .snd = isProp∃ _ _

    p? : ℙ ⟨ P s G.pt₀ ⟩
    p? p = ST.rec isSetHProp (fix₀ p) ∣f∣

  E : (sh : Sh) → hGroup _
  E sh = ΠGroup T (Eᴰ sh)

  Wᴰ : (sh : Sh) → ∀ t → hAction _ (Eᴰ sh t)
  Wᴰ sh@(s , ∣f∣) t = WrAction (Stabℙ (G s) (P s) (Eᴰ.p? s ∣f∣ t)) (StabℙAction-alt (G s) (P s) (Eᴰ.p? s ∣f∣ t)) (H t) (Q t)

  W : (sh : Sh) → hAction _ (E sh)
  W sh = ΠActionΣ (T , is-set-T) (Eᴰ sh) (Wᴰ sh)

  E-β : (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) → ⟨ E (s , ST.∣ g , f ∣₂) ⟩ᵗ ≡ Σ ((t : T) → {! !}) _
  E-β s g f = refl
  -- W-β : (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) → W (s , ST.∣ g , f ∣₂) ≡ 

  module * (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) where
    fix : (t : T) → ℙ ⟨ P s g ⟩
    fix t p .fst = f p ≡ t
    fix t p .snd = is-set-T (f p) t

    fix₀ : (t : T) → ℙ ⟨ P s G.pt₀ ⟩
    fix₀ t p₀ .fst = ∃[ γ ∈ G.pt₀ ≡ g ] f (subst (λ - → ⟨ P s - ⟩) γ p₀) ≡ t
    fix₀ t p₀ .snd = isProp∃ _ _

    fix₀⇔env₀ : ∀ t p → ⟨ fix₀ t p ⟩ ≃ ⟨ env₀ s t p ⟩
    fix₀⇔env₀ t p = propBiimpl→Equiv {! !} {! !}
      -- (PT.map λ { (γ , fix) → f ∘ subst (λ - → ⟨ P s - ⟩) γ , refl , cong (f ∘ subst (λ - → ⟨ P s - ⟩) γ) (substRefl {B = λ - → ⟨ P s - ⟩} p) ∙ fix })
      -- (PT.map λ { (γ , fix) → f ∘ subst (λ - → ⟨ P s - ⟩) γ , fix })
      (PT.rec {! !} λ { (γ , ≡t) → λ { g' f' → ∃-intro {! !} {! !} } })
      λ env → env g f
      -- (λ env → do
      --   (f' , xx) ← env
      --   ∃-intro {! !} {!xx !}
      -- )

    {-
    Fib' : (t : T) → hAction ℓ (G s)
    Fib' t g' .fst = Σ[ f' ∈ (⟨ P s g' ⟩ → T) ] (fiber f' t) ≃ (fiber f t)
    Fib' t g' .snd = {! !}

    fix' : (t : T) → ⟨ Fib' t g ⟩
    fix' t .fst = f
    fix' t .snd = {! !}

    -- fix' t p .fst = f p ≡ t
    -- fix' t p .snd = is-set-T (f p) t

    G∣' : (t : T) → hGroup ℓ
    G∣' t = Stab' (G s) (Fib' t) g (f , {! !})
    -}

  {-
    Fib' : hAction (ℓ-suc ℓ) (G s)
    Fib' g .fst = (g ≡ G.pt₀) × ℙ ⟨ P s g ⟩
    Fib' g .snd = isSet× (G.is-groupoid _ _) isSetℙ

    fix' : (t : T) → ℙ ⟨ P s g ⟩
    fix' t p .fst = f p ≡ t
    fix' t p .snd = is-set-T (f p) t

    G' : (t : T) → hGroup (ℓ-suc ℓ)
    G' t = pointedConnectedGroupoid→hGroup G'ᵗ {! !} {! !} {! !} where
      G'ᵗ : Type _
      G'ᵗ = Σ[ g ∈ ⟨ G s ⟩ᵗ ] ∃[ α ∈ g ≡ G.pt₀ ] {! !}

      g₀ : G'ᵗ
      g₀ .fst = G.pt₀
      g₀ .snd = ∃-intro refl {! !}
  -}

    -- G∣-sub : (t : T) → Subgroup (ℓ-suc ℓ) (G s)
    -- G∣-sub t .fst = Fib
    -- G∣-sub t .snd .fst = λ (p₀ : ⟨ P s G.pt₀ ⟩) → (∃[ γ ∈ G.pt₀ ≡ g ] f (subst (λ - → ⟨ P s - ⟩) γ p₀) ≡ t) , {! !}
    -- G∣-sub t .snd .snd = isPathConnectedΣ (G.is-connected) λ g → {! !}

    G∣ : (t : T) → hGroup (ℓ-suc ℓ)
    G∣ t = Stabℙ' (G s) (P s) (fix t)

    G₀ : (t : T) → hGroup (ℓ-suc ℓ)
    G₀ t = Stabℙ (G s) (P s) (fix₀ t)

    G∣-proj : (t : T) → ⟨ G∣ t ⟩ᵗ → ⟨ G s ⟩ᵗ
    G∣-proj t ((g , _) , _) = g

    G∣↪ : ∀ t → ⟨ G∣ t ⟩ᵗ ↪ ⟨ ∫ (G s) Fib ⟩
    G∣↪ t = StabEmbedding' (G s) Fib g (fix t)

    G∣-emb : (t : T) → Embedding ⟨ ∫ (G s) Fib ⟩ (ℓ-suc ℓ)
    G∣-emb t .fst = ⟨ G∣ t ⟩ᵗ
    G∣-emb t .snd = G∣↪ t

  {-
    G∣-proj : (t : T) → hGroupHom (G∣ t) (G s)
    G∣-proj t = mkHGroupHom (G∣ t) (G s) π {! !} where
      π : ⟨ G∣ t ⟩ᵗ → ⟨ G s ⟩ᵗ
      π ((g , _) , _) = g

      π-pres-pt₀ : π (hGroup.pt₀ (G∣ t)) ≡ G.pt₀
      π-pres-pt₀ = {! !}
  -}

    P∣ : (t : T) → hAction ℓ (G∣ t)
    P∣ t = Pᴰ t ∘ fst

    P₀ : (t : T) → hAction ℓ (G₀ t)
    P₀ t = Pᴰ t ∘ fst

    H∣ : (t : T) → ⟨ G∣ t ⟩ᵗ → hGroup ℓ
    H∣ t ((g' , fib) , _) = FunGroup (Σ[ p ∈ ⟨ P s g' ⟩ ] ⟨ fib p ⟩) (H t)

    H₀ : (t : T) → ⟨ G₀ t ⟩ᵗ → hGroup ℓ
    H₀ t ((g' , fib) , _) = FunGroup (Σ[ p ∈ ⟨ P s g' ⟩ ] ⟨ fib p ⟩) (H t)

    Grᴰ : T → hGroup (ℓ-suc ℓ)
    Grᴰ t = G∣ t ≀[ P∣ t ] H t

    Grᴰ₀ : T → hGroup (ℓ-suc ℓ)
    Grᴰ₀ t = G₀ t ≀[ P₀ t ] H t

    Grᴰ↪ : (t : T) → ⟨ Grᴰ t ⟩ᵗ ↪ (Σ[ (g , fix) ∈ ⟨ ∫ (G s) Fib ⟩ ] ⟨ FunGroup ⟨ Pᴰ t (g , fix) ⟩ (H t) ⟩ᵗ)
    Grᴰ↪ t = Σ-embed-fst (G∣↪ t)

    Grᴰ-emb : (t : T) → Embedding (Σ[ (g , fix) ∈ ⟨ ∫ (G s) Fib ⟩ ] ⟨ FunGroup ⟨ Pᴰ t (g , fix) ⟩ (H t) ⟩ᵗ) (ℓ-suc ℓ)
    Grᴰ-emb t .fst = ⟨ Grᴰ t ⟩ᵗ
    Grᴰ-emb t .snd = Grᴰ↪ t

    Gr* : hGroup (ℓ-suc ℓ)
    Gr* = ΠGroup T Grᴰ

    Gr₀ : hGroup (ℓ-suc ℓ)
    Gr₀ = ΠGroup T Grᴰ₀

    {-
    Grᴰ₀↪Envᴰ : ∀ t → hGroupHom (Grᴰ₀ t) (Envᴰ s t)
    Grᴰ₀↪Envᴰ t = mkHGroupHom (Grᴰ₀ t) (Envᴰ s t) ι ι-pres-pt₀ where
      ι : ⟨ Grᴰ₀ t ⟩ᵗ → ⟨ Envᴰ s t ⟩ᵗ
      ι (g₀ , η , η-conn) = _ , η ∘ (p* g₀) , ST.merePath→pathSetTrunc ηp*-conn where
        p* : (g₀@((g' , fib') , fib-conn) : ⟨ G₀ t ⟩ᵗ)
          → (Σ[ p ∈ ⟨ P s g' ⟩ ] ∀ (f : (⟨ P s g' ⟩ → T)) → f p ≡ t)
          → (Σ[ p ∈ ⟨ P s g' ⟩ ] ⟨ fib' p ⟩)
        p* g₀ (p , _) .fst = p
        p* g₀ p-fix .snd = hGroup.elimProp (G₀ t) {P = λ { ((g' , fib') , _) → ((p , _) : Σ[ p ∈ ⟨ P s g' ⟩ ] ∀ (f : (⟨ P s g' ⟩ → T)) → f p ≡ t) → ⟨ fib' p ⟩ } }
          (λ { g₀@((g' , fib') , fib-conn) → isPropΠ λ (p , _) → str (fib' p) })
          (λ where
            (p' , fix-p) → do
              pt₀≡g ← G.mere-path g
              ∃-intro pt₀≡g $ fix-p (f ∘ subst (λ - → ⟨ P s - ⟩) pt₀≡g)
          )
          g₀ p-fix

        ηp*-conn : PT.∥ (η ∘ p* g₀) ≡ const (hGroup.pt₀ (H t)) ∥₁
        ηp*-conn = do
          η≡const-pt₀ ← ST.pathSetTrunc→merePath η-conn
          return $ cong (_∘ p* g₀) η≡const-pt₀

      ι-pres-pt₀ : ι (hGroup.pt₀ (Grᴰ₀ t)) ≡ hGroup.pt₀ (Envᴰ s t)
      ι-pres-pt₀ = ΣPathP (refl , FunGroupPath _ (H t) refl )
    -}

    Grᴰ₀↪Envᴰ' : ∀ t → hGroupMono (Grᴰ₀ t) (Envᴰ s t)
    Grᴰ₀↪Envᴰ' t = {! ≀-map-fst-mono (G₀ t) (G s) (EnvAct s t) (H t)   !}

    Grᴰ₀↪Envᴰ : ∀ t → hGroupMono (Grᴰ₀ t) (Envᴰ s t)
    Grᴰ₀↪Envᴰ t = ≀-map-mono
      (G₀ t) (G s)
      (P₀ t) (EnvAct s t)
      (H t) (H t)
      (StabℙMono (G s) (P s) (fix₀ t) .snd)
      {! shift !}
      (idHGroupMono (H t))
      where
        shift? : (g₀@((g' , fib') , fib-conn) : ⟨ G₀ t ⟩ᵗ) → ((p' , _) : ⟨ EnvAct s t g' ⟩) → ⟨ fib' p' ⟩
        shift? = hGroup.elimProp (G₀ t) (λ { g₀@((_ , fib') , _) → isPropΠ (λ (p' , _) → str $ fib' p') }) λ where
          (p' , _≡t) → do
            pt₀≡g ← G.mere-path g
            ∃-intro pt₀≡g $ (f ∘ subst (λ - → ⟨ P s - ⟩) pt₀≡g) ≡t

        shift : (g₀@((g' , fib') , fib-conn) : ⟨ G₀ t ⟩ᵗ) → ⟨ EnvAct s t g' ⟩ → ⟨ P₀ t g₀ ⟩
        shift g₀ (p' , ≡t) .fst = p'
        shift g₀ e .snd = shift? g₀ e

        unshift : (g₀@((g' , fib') , fib-conn) : ⟨ G₀ t ⟩ᵗ) → ⟨ P₀ t g₀ ⟩ → ⟨ EnvAct s t g' ⟩
        unshift g₀ (p' , _) .fst = p'
        -- unshift g₀ (e) .snd = hGroup.elimProp (G₀ t) {P = λ g₀ → ⟨ P₀ t g₀ ⟩ → ⟨  ?} {! !} {! !} g₀ e
        unshift g₀ (p' , fix-t) .snd = hGroup.elimProp (G₀ t) {P = λ g₀ @ ((g , fib) , _) → (p' : ⟨ P s g ⟩) → ⟨ fib p' ⟩ → (f : ⟨ P s g ⟩ → T) → f p' ≡ t}
          {! !}
          (λ p fib f' → PT.untrunc (is-set-T _ _) do
            (symm , f-≡t) ← fib
            return {! !}
          )
          g₀
          p'
          fix-t

    {-
    is-mono-Grᴰ₀↪Envᴰ : ∀ t → isMono (Grᴰ₀ t) (Envᴰ s t) (Grᴰ₀↪Envᴰ t)
    is-mono-Grᴰ₀↪Envᴰ t = goal where
      fiber-equiv : (e : ⟨ Envᴰ s t ⟩ᵗ) → {! !} ≃ (fiber (Grᴰ₀↪Envᴰ t .fst) e)
      fiber-equiv e@(g' , p-fix) =
        {! !}
          ≃⟨ {! !} ⟩

        Σ[ fib' ∈ ℙ ⟨ P s g' ⟩ ]
        Σ[ fib-conn ∈ ST.∣ g' , fib' ∣₂ ≡ ST.∣ G.pt₀ , fix₀ t ∣₂ ]
        Σ[ η ∈ ⟨ FunGroup ⟨ Pᴰ t (g' , fib') ⟩ (H t) ⟩ᵗ ]
          Path (⟨ FunGroup ⟨ EnvAct s t _ ⟩ (H t) ⟩ᵗ) (Grᴰ₀↪Envᴰ t .fst (((g' , fib') , fib-conn) , η) .snd) p-fix

          ≃⟨ {! !} ⟩

        Σ[ (g'' , h₀) ∈ singl g' ] Σ[ fib'' ∈ ℙ ⟨ P s g'' ⟩ ]
        Σ[ fib-conn ∈ ST.∣ g'' , fib'' ∣₂ ≡ ST.∣ G.pt₀ , fix₀ t ∣₂ ]
        Σ[ η ∈ ⟨ FunGroup ⟨ Pᴰ t (g'' , fib'') ⟩ (H t) ⟩ᵗ ]
          PathP (λ i → ⟨ FunGroup ⟨ EnvAct s t (h₀ (~ i)) ⟩ (H t) ⟩ᵗ) (Grᴰ₀↪Envᴰ t .fst (((g'' , fib'') , fib-conn) , η) .snd) p-fix

          ≃⟨ strictEquiv
            (λ { ((g'' , h₀) , (fib'' , (fib''-conn , (η , h₁)))) → (((g'' , fib'') , fib''-conn) , η) , sym h₀ , h₁ })
            (λ { ((((g'' , fib'') , fib''-conn) , η) , h₀ , h₁) → ((g'' , sym h₀) , (fib'' , (fib''-conn , (η , h₁)))) })
          ⟩

        Σ[ g₀@(((g'' , fib'') , _) , _) ∈ ⟨ Grᴰ₀ t ⟩ᵗ ] Σ[ h₀ ∈ g'' ≡ g' ] PathP _ _ p-fix
          ≃⟨ Σ-cong-equiv-snd (λ g₀ → ΣPathP≃PathPΣ) ⟩
        Σ[ g₀ ∈ ⟨ Grᴰ₀ t ⟩ᵗ ] (Grᴰ₀↪Envᴰ t .fst g₀) ≡ (g' , p-fix)
          ≃⟨⟩
        (fiber (Grᴰ₀↪Envᴰ t .fst) e)
          ≃∎

      goal : ∀ e → isSet (fiber (Grᴰ₀↪Envᴰ t .fst) e)
      goal = {! !}
    -}

    Grᴰ₀-Mono : ∀ t → Mono _ (Envᴰ s t)
    Grᴰ₀-Mono t .fst = Grᴰ₀ t
    Grᴰ₀-Mono t .snd = Grᴰ₀↪Envᴰ t

    -- TODO: Show that this is actually an embedding
    Grᴰ↪Envᴰ : ∀ t → Mono _ (Envᴰ s t)
    Grᴰ↪Envᴰ t .fst = Grᴰ t
    Grᴰ↪Envᴰ t .snd .fst = mkHGroupHom (Grᴰ t) (Envᴰ s t) {! !} {! !}
      -- ι : ⟨ Grᴰ t ⟩ᵗ → ⟨ Envᴰ s t ⟩ᵗ
      -- ι (((g' , fib') , fib-conn) , (η , _)) = g' , η* , {! !} where
      --   η* : (Σ[ f ∈ (⟨ P s g' ⟩ → T) ] Σ[ p ∈ ⟨ P s g' ⟩ ] f p ≡ t) → ⟨ H t ⟩ᵗ
      --   η* (f , p , f-const) = η (p , ST.pathSetTrunc→recProp (str (fib' p)) {! !} fib-conn)

      -- ι-pres-pt₀ : ι (hGroup.pt₀ (Grᴰ t)) ≡ hGroup.pt₀ (Envᴰ s t)
      -- ι-pres-pt₀ = ΣPathP ({! !} , {! !})
    Grᴰ↪Envᴰ t .snd .snd = {! !}

    Gr*↪ : ⟨ Gr* ⟩ᵗ ↪ (∀ t → (Σ[ (g , fix) ∈ ⟨ ∫ (G s) Fib ⟩ ] ⟨ FunGroup ⟨ Pᴰ t (g , fix) ⟩ (H t) ⟩ᵗ))
    Gr*↪ = compEmbedding
      {B = ∀ t → ⟨ Grᴰ t ⟩ᵗ}
      (Π-codomain-embed Grᴰ↪)
      (ΠGroupEmbedding T Grᴰ)

    Gr*-emb : Embedding ((t : T) → (Σ[ (g , fix) ∈ ⟨ ∫ (G s) Fib ⟩ ] ⟨ FunGroup ⟨ Pᴰ t (g , fix) ⟩ (H t) ⟩ᵗ)) (ℓ-suc ℓ)
    Gr*-emb .fst = ⟨ Gr* ⟩ᵗ
    Gr*-emb .snd = Gr*↪
  
  ⟨Gr-emb⟩ : (sh@(s , _) : Sh) → Embedding ((t : T) → (Σ[ (g , fix) ∈ ⟨ ∫ (G s) Fib ⟩ ] ⟨ FunGroup ⟨ Pᴰ t (g , fix) ⟩ (H t) ⟩ᵗ)) (ℓ-suc ℓ)
  ⟨Gr-emb⟩ = uncurry λ s → ST.rec isSetEmbedding λ (g , f) → *.Gr*-emb s g f

  pt-fooo : (sh : Sh) → ⟨Gr-emb⟩ sh .fst
  pt-fooo = uncurry λ s → ST.elim→Gpd {! !} (λ { (g , f) → hGroup.pt₀ (*.Gr* s g f) }) {! !}

{-
    Gr*-fst : (t : T) → ⟨ Gr* ⟩ᵗ → ⟨ G s ⟩ᵗ
    Gr*-fst t (k , _) using (((g' , _) , _) , _) ← k t = g'

  {-
    Grᴰ-fst-hom : (t : T) → hGroupHom (Grᴰ t) (G s)
    Grᴰ-fst-hom t = mkHGroupHom (Grᴰ t) (G s) π {! hGroup.pt₀ (Grᴰ t) .fst .snd!} where
      π : ⟨ Grᴰ t ⟩ᵗ → ⟨ G s ⟩ᵗ
      π (((g , _) , _) , _) = g
  -}

    Psᴰ : (t : T) → hAction ℓ (Grᴰ t)
    Psᴰ t (((g' , fib) , _) , (h , _)) = ΣSet (ΣSubSet (P s g') fib) (Q t ∘ h)

    Ps* : hAction ℓ Gr*
    Ps* = ΠActionΣ (T , is-set-T) Grᴰ Psᴰ

  module UnitLeft
    (is-contr-S : isContr S)
    (is-triv-G : ∀ s → isTrivial (G s))
    (is-contr-P : ∀ s g → isContr ⟨ P s g ⟩)
    where
    private
      s₀ = is-contr-S .fst

      g₀ : {s : S} → ⟨ G s ⟩ᵗ
      g₀ {s} = is-triv-G s .fst

      p₀ : {s : S} {g : ⟨ G s ⟩ᵗ} → ⟨ P s g ⟩
      p₀ {s} {g} = is-contr-P s g .fst

      is-contr-∫ : ∀ s → isContr ⟨ ∫ (G s) (P s) ⟩
      is-contr-∫ s = isContrΣ (is-triv-G s) (is-contr-P s)

    Sh-unit-left : Sh ≃ T
    Sh-unit-left =
      Σ[ s ∈ S ] ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂ ≃⟨ Σ-contractFst is-contr-S ⟩
       ∥ Σ[ g ∈ ⟨ G s₀ ⟩ᵗ ] (⟨ P s₀ g ⟩ → T) ∥₂ ≃⟨ ST.setTruncEquiv (Σ-contractFst (is-triv-G _)) ⟩
       ∥ (⟨ P s₀ g₀ ⟩ → T) ∥₂ ≃⟨ ST.setTruncIdempotent≃ (isSet→ is-set-T) ⟩
       (⟨ P s₀ g₀ ⟩ → T) ≃⟨ Π-contractDom (is-contr-P _ _) ⟩
      T ≃∎

    module _ (f : ⟨ P s₀ g₀ ⟩ → T) where
      open * s₀ g₀ f
      is-triv-G∣ : ∀ t → isTrivial (G∣ t)
      is-triv-G∣ t = monoIntoTrivial→isTrivial (G∣ t) (G s₀) (G∣-proj t) trunc-proj (is-triv-G s₀) where
        fiber-equiv : ∀ g → fiber (G∣-proj t) g ≃ (Σ[ fix' ∈ ⟨ Fib g ⟩ ] ST.∣ (g , fix') ∣₂ ≡ ST.∣ (g₀ , fix t) ∣₂)
        fiber-equiv g =
          Σ[ ((g' , _) , _) ∈ ⟨ G∣ t ⟩ᵗ ] g' ≡ g
            ≃⟨ strictEquiv (λ { (((g' , fix') , conn) , γ) → ((g' , sym γ) , fix' , conn) }) (λ { ((g' , γ) , fix' , conn) → (((g' , fix') , conn) , sym γ) }) ⟩
          Σ[ (g' , _) ∈ singl g ] (Σ[ fix' ∈ ⟨ Fib g' ⟩ ] Path (∥ ⟨ ∫ (G s₀) Fib ⟩ ∥₂) ST.∣ (g' , fix') ∣₂ ST.∣ (g₀ , fix t) ∣₂)
            ≃⟨ Σ-contractFst (isContrSingl g) ⟩
          (Σ[ fix' ∈ ⟨ Fib g ⟩ ] ST.∣ (g , fix') ∣₂ ≡ ST.∣ (g₀ , fix t) ∣₂)
            ≃∎

        trunc-proj : isOfHLevelFun 2 (G∣-proj t)
        trunc-proj g = isOfHLevelRespectEquiv 2 (invEquiv $ fiber-equiv g) $ isSetΣ (str $ Fib g) (λ _ → ST.isSetPathImplicit)

      Gr*-unit-left : hGroupEquiv Gr* (H (f p₀))
      Gr*-unit-left =
        ΠGroup T (λ t → G∣ t ≀[ P∣ t ] H t) ≃ᴳ⟨ ΠGroupEquivCodomain (λ t → G∣ t ≀[ P∣ t ] H t) {! !} (λ t → WrContractFst (G∣ t) (P∣ t) (H t) (is-triv-G∣ t)) ⟩
        ΠGroup T (λ t → H∣ t {! !}) ≃ᴳ⟨ {! !} ⟩
        ΠGroup (Σ[ t ∈ T ] Σ[ p ∈ ⟨ P s₀ g₀ ⟩ ] f p ≡ t) (λ (t , _) → H t) ≃ᴳ⟨ {! !} ⟩
        H (f p₀) ∎ᴳ

{-
      Ps*-unit-left : ∀ k → ⟨ Ps* s₀ g₀ f k ⟩ ≃ ⟨ Q (f p₀) (Gr*-unit-left .fst .fst k) ⟩
      Ps*-unit-left (k , _) =
        (Σ[ t ∈ T ] let (((g' , fib) , _) , (h , _)) = k t in Σ[ p ∈ Σ[ p ∈ ⟨ P s₀ g' ⟩ ] ⟨ fib p ⟩ ] ⟨ Q t (h p) ⟩) ≃⟨ {! !} ⟩
        (Σ[ t ∈ T ] let (((g' , fib) , _) , (h , _)) = k t in Σ[ p? ∈ ⟨ fib p₀ ⟩ ] ⟨ Q t (h (p₀ , p?)) ⟩) ≃⟨ {! !} ⟩
        (Σ[ t ∈ T ] let (((g' , fib) , _) , (h , _)) = k t in Σ[ p? ∈ f p₀ ≡ t ] ⟨ Q t (h (p₀ , {! !})) ⟩) ≃⟨ {! !} ⟩
        (let (((g' , fib) , _) , (h , _)) = k (f p₀) in ⟨ Q (f p₀) (h (p₀ , {! refl′ (f p₀) !})) ⟩) ≃⟨ {! !} ⟩
        {! !} ≃∎

  module UnitRight
    (is-contr-T : isContr T)
    (is-triv-H : ∀ t → isTrivial (H t))
    (is-contr-Q : ∀ t h → isContr ⟨ Q t h ⟩)
    where
    private
      t₀ = is-contr-T .fst

      h₀ : {t : T} → ⟨ H t ⟩ᵗ
      h₀ {t} = is-triv-H t .fst

      q₀ : {t : T} {h : ⟨ H t ⟩ᵗ} → ⟨ Q t h ⟩
      q₀ {t} {h} = is-contr-Q t h .fst

    Sh-unit-right : Sh ≃ S
    Sh-unit-right =
      Σ[ s ∈ S ] ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂ ≃⟨ Σ-cong-equiv-snd (λ s → ST.setTruncEquiv (Σ-contractSnd (λ g → isContrΠ λ _ → is-contr-T))) ⟩
      Σ[ s ∈ S ] ∥ ⟨ G s ⟩ᵗ ∥₂ ≃⟨ Σ-contractSnd (λ s → hGroup.is-connected (G s)) ⟩
      S ≃∎

    module _ (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) where
      Gr*-unit-right : hGroupEquiv (Gr* s g f) (G s)
      Gr*-unit-right =
        ΠGroup T (λ t → Aut (∫ (G _) (Fib _ _ f)) (fib₀ _ _ f t) ⋉ λ ((g' , fib) , _) → FunGroup (Σ[ p ∈ ⟨ P s g' ⟩ ] ⟨ fib p ⟩) (H t)) ≃ᴳ⟨ {! !} ⟩
        (Aut (∫ (G _) (Fib _ _ f)) (fib₀ _ _ f t₀) ⋉ λ ((g' , fib) , _) → FunGroup (Σ[ p ∈ ⟨ P s g' ⟩ ] ⟨ fib p ⟩) (H t₀)) ≃ᴳ⟨ ⋉-contractSnd {! !} ? {! !} ⟩
        (Aut (∫ (G _) (Fib _ _ f)) (fib₀ _ _ f t₀)) ≃ᴳ⟨ {! !} ⟩
        (G s) ∎ᴳ

      Ps*-unit-right : ∀ k → ⟨ Ps* s g f k ⟩ ≃ ⟨ P s g ⟩
      Ps*-unit-right k*@(k , _) =
        (Σ[ t ∈ T ] let (((g' , fib) , _) , (h , _)) = k t in Σ[ p ∈ Σ[ p ∈ ⟨ P s g' ⟩ ] ⟨ fib p ⟩ ] ⟨ Q t (h p) ⟩)

          ≃⟨ Σ-contractFst is-contr-T ⟩

        (let (((g' , fib) , _) , (h , _)) = k t₀ in Σ[ p ∈ Σ[ p ∈ ⟨ P s g' ⟩ ] ⟨ fib p ⟩ ] ⟨ Q t₀ (h p) ⟩)

          ≃⟨ Σ-contractSnd (λ p → is-contr-Q _ _) ⟩

        (let (((g' , fib) , _) , (h , _)) = k t₀ in Σ[ p ∈ ⟨ P s g' ⟩ ] ⟨ fib p ⟩)

          ≃⟨ Σ-contractSnd (λ p → let (((g' , fib) , g'fib-conn) , (h , _)) = k t₀ in inhProp→isContr (lemma p) (str (fib p))) ⟩

        ⟨ P s (Gr*-fst _ _ _ t₀ k*) ⟩

          ≃⟨ {! !} ⟩

        ⟨ P s g ⟩ ≃∎
          where
          lemmaer :
            let (((g' , fib) , _) , _) = k t₀
            in ((g' , fib) ≡ fib₀ s g f t₀) → (p : ⟨ P s g' ⟩) → ⟨ fib p ⟩
          lemmaer htpy = subst (λ (xx : Σ[ g ∈ ⟨ G s ⟩ᵗ ] ⟨ Fib _ _ f g ⟩ ) → (p : ⟨ P s (xx .fst) ⟩) → ⟨ xx .snd p ⟩) (sym htpy)
            λ p → the (f p ≡ t₀) (isContr→isProp is-contr-T (f p) t₀)

          lemma : let (((g' , fib) , g'fib-conn) , (h , _)) = k t₀ in (p : ⟨ P s g' ⟩) → ⟨ fib p ⟩
          lemma = let (((g' , fib) , g'fib-conn) , (h , _)) = k t₀ in λ where
            → ST.pathSetTrunc→recProp (isPropΠ λ p → str (fib p)) lemmaer g'fib-conn
            -}
          -}
