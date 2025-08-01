{-# OPTIONS --lossy-unification #-}
open import GpdCont.Prelude hiding (_▷_)

module GpdCont.ActionContainer.Composition (ℓ : Level) where

open import GpdCont.Prelude.Notation using (_>>=_ ; pure)
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
open import GpdCont.PropositionalTruncation as PT using (∥_∥₁)
open import GpdCont.Embedding
open import GpdCont.Connectivity

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Logic using (⊤)
open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

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
    _▷_ : ∀ {s} {g₀ g₁ : ⟨ G s ⟩ᵗ} → g₀ ≡ g₁ → ⟨ P s g₀ ⟩ → ⟨ P s g₁ ⟩
    γ ▷ p = subst (λ g → ⟨ P _ g ⟩) γ p

  Shᴰ : S → Type ℓ
  Shᴰ s = ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂

  Sh : Type ℓ
  Sh = Σ S Shᴰ

  -- The subset of positions (p₀ : P s pt₀) such that f p₀ ≡ t for any (f : ⟨ P s g ⟩ → T) , modulo transport.
  Fix* : {s : S} (t : T) → (Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T)) → ℙ ⟨ P s G.pt₀ ⟩
  Fix* t (g , f) p₀ .fst = ∃[ γ ∈ G.pt₀ ≡ g ] f (γ ▷ p₀) ≡ t
  Fix* t (g , f) p₀ .snd = isProp∃ _ _

  perm : {s : S} {t : T} {g : ⟨ G s ⟩ᵗ} {f : ⟨ P s g ⟩ → T}
    → (p₀ : ⟨ P s G.pt₀ ⟩)
    → ⟨ Fix* t (g , f) p₀ ⟩
    → ⟨ P s g ⟩
  perm p₀ = PT.rec→Set (str (P _ _))
    (λ where
      (γ , fγ≡t) → γ ▷ p₀
    )
    λ where
      (γ , fγ≡t) (δ , fδ≡t) → {! fγ≡t ∙ sym fδ≡t !}


  Fix⁰ : {s : S} (t : T) → (Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T)) → ℙ ⟨ P s G.pt₀ ⟩
  Fix⁰ t (g , f) p₀ .fst = ∃[ p ∈ ⟨ P _ g ⟩ ] Σ[ γ ∈ G.pt₀ ≡ g ] PathP (λ i → ⟨ P _ (γ i) ⟩) p₀ p × (f p ≡ t)
  Fix⁰ t (g , f) p₀ .snd = {! !}

  Fix : (t : T) (sh : Sh) → ℙ ⟨ P (sh .fst) G.pt₀ ⟩
  Fix t = uncurry λ s → ST.rec (isSet→ isSetHProp) $ Fix* t

  module Restrict (sh @ (s , _) : Sh) where
    G∣f : T → hGroup _
    G∣f t = Stabℙ (G s) (P s) (Fix t sh)

    P∣f : ∀ t → hAction _ (G∣f t)
    P∣f t = StabℙAction-alt (G s) (P s) (Fix t sh)

  module _ (sh : Sh) where
    open Restrict sh
    Grᴰ : T → hGroup (ℓ-suc ℓ)
    Grᴰ t = G∣f t ≀[ P∣f t ] H t

    Psᴰ : ∀ t → hAction ℓ (Grᴰ t)
    Psᴰ t = WrAction (G∣f t) (P∣f t) (H t) (Q t)

    Gr : hGroup (ℓ-suc ℓ)
    Gr = ΠGroup T Grᴰ

    Ps : hAction ℓ Gr
    Ps = ΠActionΣ (T , is-set-T) Grᴰ Psᴰ

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

    fix! : ∀ t sh p → ⟨ Fix t sh p ⟩
    fix! t = uncurry λ s → ST.elim (λ ∣f∣ → isSetΠ λ p → isProp→isSet (str (Fix t (s , ∣f∣) p))) λ where
      (g , f) p → do
        pt₀≡g ← G.mere-path g
        ∃-intro pt₀≡g (isContr→isProp is-contr-T _ t)

    -- fix⁰! : ∀ {s} (t : T) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) → ∀ p₀ → ⟨ Fix⁰ t (g , f) p₀ ⟩
    -- fix⁰! t g f p₀ .fst .fst = {! !}
    -- fix⁰! t g f p₀ .fst .snd = {! !}
    -- fix⁰! t g f p₀ .snd = {! !}

    module _ (sh@(s , ∣f∣) : Sh) where
      open Restrict sh

      isContrFix : ∀ t p → isContr ⟨ Fix t sh p ⟩
      isContrFix t p = inhProp→isContr (fix! t sh p) (str $ Fix t sh p)

      isContrFixAut : (t : T) (g| @ (aut (g , fix)) : ⟨ G∣f t ⟩ᵗ) → ∀ p → isContr ⟨ fix p ⟩
      isContrFixAut t = hGroup.elimProp (G∣f t) (λ _ → isPropΠ λ p → isPropIsContr) $ isContrFix t

      Fix≡⊤ : ∀ t p → ⟨ Fix t sh p ⟩ ≡ ⟨ ⊤ ⟩
      Fix≡⊤ t p = isContr→≡Unit* (isContrFix t p)

      G∣f-full-equiv : ∀ t → hGroupEquiv (G∣f t) (G s)
      G∣f-full-equiv t =
        G∣f t
          ≃ᴳ⟨ StabℙCongEquiv (G s) (P s) (Fix t sh) (λ _ → ⊤) (Fix≡⊤ t) ⟩
        (Stabℙ (G s) (P s) (λ _ → ⊤))
          ≃ᴳ⟨ StabℙAllEquiv (G s) (P s) ⟩
        G s
          ∎ᴳ

      Gr-unit-right : hGroupEquiv (Gr sh) (G s)
      Gr-unit-right =
        ΠGroup T (λ t → G∣f t ≀[ P∣f t ] H t)
          -- Contract away the domain T
          ≃ᴳ⟨ ΠGroupContractDomain T (Grᴰ sh) is-contr-T ⟩
        G∣f t₀ ≀[ P∣f t₀ ] H t₀
          -- Contract the trivial second projection Hₜ of the wreath product
          ≃ᴳ⟨ WrContractSnd (G∣f t₀) (P∣f t₀) (H t₀) (is-triv-H t₀) ⟩
        G∣f t₀
          -- Since any (f : ⟨ P s g ⟩ → T) must map to t₀, G∣f is the entire group Gₛ:
          ≃ᴳ⟨ G∣f-full-equiv t₀ ⟩
        G s
          ∎ᴳ

      Gr→G : ⟨ Gr sh ⟩ᵗ → ⟨ G s ⟩ᵗ
      Gr→G = Gr-unit-right .hGroupEquiv.fun

      Ps-unit-right : ∀ k → ⟨ Ps sh k ⟩ ≃ ⟨ P s (Gr→G k) ⟩
      Ps-unit-right k*@(aut k) =
        (Σ[ t ∈ T ] let (aut (g , fix) , aut h) = k t in Σ[ p ∈ Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ fix p ⟩ ] ⟨ Q t (h p) ⟩)
          ≃⟨ Σ-contractFst is-contr-T ⟩
        (let (aut (g , fix) , aut h) = k t₀ in Σ[ p ∈ Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ fix p ⟩ ] ⟨ Q t₀ (h p) ⟩)
          ≃⟨ Σ-contractSnd (λ p → is-contr-Q _ _) ⟩
        (let (aut (g , fix) , _) = k t₀ in Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ fix p ⟩)
          ≃⟨ Σ-contractSnd (λ p → let (g∣ , _) = k t₀ in isContrFixAut t₀ g∣ p) ⟩
        ⟨ P s (Gr→G k*) ⟩
          ≃∎

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

    opaque
      Sh-unit-left-β : {s : S} {g : ⟨ G s ⟩ᵗ} (f : ⟨ P s g ⟩ → T) → equivFun Sh-unit-left (s , ST.∣ g , f ∣₂) ≡ f p₀
      Sh-unit-left-β {s} {g} f = transportRefl {A = T} _ ∙ transportRefl {A = T} _ ∙ cong f (isContr→isProp (is-contr-P _ _) _ _)

    module _ (t : T) (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) (p : ⟨ P s G.pt₀ ⟩) where
      private
        t₀ : T
        t₀ = equivFun Sh-unit-left (s , ST.∣ g , f ∣₂)

        is-contr-path-G : isContr (G.pt₀ ≡ g)
        is-contr-path-G = isOfHLevelPath 0 (is-triv-G s) G.pt₀ g

        t₀≡f : t₀ ≡ f (subst (λ - → ⟨ P s - ⟩) (is-contr-path-G .fst) p)
        t₀≡f =
          t₀ ≡⟨ Sh-unit-left-β f ⟩
          f p₀ ≡⟨ cong f (is-contr-P _ _ .snd _) ⟩
          f (subst (λ - → ⟨ P s - ⟩) _ p) ∎

      Fix-equiv* : (t₀ ≡ t) ≃ (∃[ γ ∈ G.pt₀ ≡ g ] f (subst (λ - → ⟨ P s - ⟩) γ p) ≡ t)
      Fix-equiv* =
        (t₀ ≡ t)
          ≃⟨ compPathlEquiv $ sym t₀≡f ⟩
        f (subst (λ - → ⟨ P s - ⟩) _ p) ≡ t
          ≃⟨ invEquiv $ PT.propTruncIdempotent≃ (is-set-T _ _) ⟩
        ∥ f (subst (λ - → ⟨ P s - ⟩) _ p) ≡ t ∥₁
          ≃⟨ invEquiv $ PT.propTrunc≃ $ Σ-contractFst $ is-contr-path-G ⟩
        ∃[ γ ∈ G.pt₀ ≡ g ] f (subst (λ - → ⟨ P s - ⟩) γ p) ≡ t
          ≃∎
    Fix-equiv : ∀ t sh p → (equivFun Sh-unit-left sh ≡ t) ≃ ⟨ Fix t sh p ⟩
    Fix-equiv t = uncurry λ s → ST.elim (λ ∣f∣ → isSetΠ λ p → isOfHLevel⁺≃ₗ 1 $ isProp→isSet $ is-set-T _ _) λ where
      (g , f) → Fix-equiv* t s g f
        
    module _ (sh@(s , ∣f∣) : Sh) where
      open Restrict sh

      is-triv-G∣f : ∀ t → isTrivial (G∣f t)
      is-triv-G∣f t = isTrivial→isTrivialMono (G s) (is-triv-G s) (StabℙMono (G s) (P s) (Fix t sh))

      t₀ : T
      t₀ = equivFun Sh-unit-left sh
      
      ΣP∣f-equiv : (singl (equivFun Sh-unit-left sh)) ≃ (Σ[ t ∈ T ] ⟨ P∣f t (hGroup.pt₀ (G∣f t)) ⟩)
      ΣP∣f-equiv =
        (singl (equivFun Sh-unit-left sh))
          ≃⟨⟩
        (Σ[ t ∈ T ] (equivFun Sh-unit-left sh ≡ t))
          ≃⟨ Σ-cong-equiv-snd (λ t → invEquiv $ Σ-contractFst (is-contr-P _ _)) ⟩
        (Σ[ t ∈ T ] Σ[ p ∈ ⟨ P s G.pt₀ ⟩ ] (equivFun Sh-unit-left sh ≡ t))
          ≃⟨ Σ-cong-equiv-snd (λ t → Σ-cong-equiv-snd $ Fix-equiv t sh) ⟩
        (Σ[ t ∈ T ] Σ[ p ∈ ⟨ P s G.pt₀ ⟩ ] ⟨ Fix t sh p ⟩)
          ≃⟨⟩
        (Σ[ t ∈ T ] ⟨ P∣f t (hGroup.pt₀ (G∣f t)) ⟩)
          ≃∎

      is-contr-ΣP∣f : isContr (Σ[ t ∈ T ] ⟨ P∣f t (hGroup.pt₀ (G∣f t)) ⟩)
      is-contr-ΣP∣f = isOfHLevelRespectEquiv 0 ΣP∣f-equiv $ isContrSingl _

      ΣP∣f-equiv' : (γ : ∀ t → ⟨ G∣f t ⟩ᵗ) → (Σ[ t ∈ T ] ⟨ P∣f t (hGroup.pt₀ (G∣f t)) ⟩) ≃ (Σ[ t ∈ T ] ⟨ P∣f t (γ t) ⟩)
      ΣP∣f-equiv' γ = substEquiv (λ (γ : ∀ t → ⟨ G∣f t ⟩ᵗ) → (Σ[ t ∈ T ] ⟨ P∣f t (γ t) ⟩)) (isPropΠ (λ t → isContr→isProp (is-triv-G∣f t)) _ γ)

      is-contr-ΣP∣f' : (γ : ∀ t → ⟨ G∣f t ⟩ᵗ) → isContr (Σ[ t ∈ T ] ⟨ P∣f t (γ t) ⟩)
      is-contr-ΣP∣f' γ = isOfHLevelRespectEquiv 0 (ΣP∣f-equiv' γ) is-contr-ΣP∣f

      Gr-unit-left : hGroupEquiv (Gr sh) (H t₀)
      Gr-unit-left =
        ΠGroup T (λ t → G∣f t ≀[ P∣f t ] H t)
          -- G∣f is a subgroup of the trivial group Gₛ
          ≃ᴳ⟨
            ΠGroupEquivCodomain
              (λ t → G∣f t ≀[ P∣f t ] H t)
              (λ t → FunGroup ⟨ P∣f t (hGroup.pt₀ (G∣f t)) ⟩ (H t))
              (λ t → WrContractFst (G∣f t) (P∣f t) (H t) (is-triv-G∣f t))
          ⟩
        ΠGroup T (λ t → FunGroup ⟨ P∣f t (hGroup.pt₀ (G∣f t)) ⟩ (H t))
          -- Currying of the product groups
          ≃ᴳ⟨ ΠGroupCurryEquiv {K = T} {L = λ t → ⟨ P∣f t (hGroup.pt₀ (G∣f t)) ⟩} (const ∘ H) ⟩
        ΠGroup (Σ[ t ∈ T ] ⟨ P∣f t (hGroup.pt₀ (G∣f t)) ⟩) (H ∘ fst)
          -- There is a unique (t₀ : T) in the image of ∣f∣
          ≃ᴳ⟨ ΠGroupContractDomain (Σ[ t ∈ T ] ⟨ P∣f t (hGroup.pt₀ (G∣f t)) ⟩) (H ∘ fst) is-contr-ΣP∣f ⟩
        H t₀
          ∎ᴳ

      Gr→H : ⟨ Gr sh ⟩ᵗ → ⟨ H t₀ ⟩ᵗ
      Gr→H = Gr-unit-left .hGroupEquiv.fun

      is-contr-ΣP∣f'' : (k : ⟨ Gr sh ⟩ᵗ) → isContr (Σ[ t ∈ T ] ⟨ P∣f t (k .fst t .fst) ⟩)
      is-contr-ΣP∣f'' k = inhProp→isContr (t₀ , {!Gr→H k  !}) {! !}

      Ps-unit-left : ∀ k → ⟨ Ps sh k ⟩ ≃ ⟨ Q t₀ (Gr→H k) ⟩
      Ps-unit-left k*@(aut k) =
        (Σ[ t ∈ T ] let (g∣ , aut h) = k t in Σ[ p ∈ ⟨ P∣f t g∣ ⟩  ] ⟨ Q t (h p) ⟩)
          ≃⟨ invEquiv Σ-assoc-≃ ⟩
        (Σ[ (t , p) ∈ Σ[ t ∈ T ] ⟨ P∣f t (k t .fst) ⟩ ] ⟨ Q t (k t .snd .fst p) ⟩)
          ≃⟨ Σ-contractFst (is-contr-ΣP∣f' (fst ∘ k)) ⟩
        ⟨ Q {! !} _ ⟩
          ≃⟨ {!  !} ⟩
        ⟨ Q t₀ (Gr→H k*) ⟩
          ≃∎
        where
          equiv : (Σ[ (t , p) ∈ Σ[ t ∈ T ] ⟨ P∣f t (k t .fst) ⟩ ] ⟨ Q t (k t .snd .fst p) ⟩) ≃ ⟨ Q t₀ (Gr→H k*) ⟩
          equiv = isoToEquiv λ where
            .Iso.fun ((t , p) , q) → {!q!}
            .Iso.inv → {! !}
            .Iso.leftInv → {! !}
            .Iso.rightInv → {! !}

  module Monoidal (X : Type ℓ) (choice : ∀ s g → ST.satChoice ⟨ P s g ⟩ ℓ) where
    module P {s} {g} = ST.Choice (choice s g)

    Sh-monoidal : {! !} ≃ {! !}
    Sh-monoidal =
      Σ[ s ∈ S ] ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → Σ[ t ∈ T ] ∥ Σ[ h ∈ ⟨ H t ⟩ᵗ ] (⟨ Q t h ⟩ → X) ∥₂) ∥₂

        ≃⟨ {! !} ⟩

      Σ[ s ∈ S ] ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] Σ[ f ∈ (⟨ P s g ⟩ → T) ] ((p : ⟨ P s g ⟩) → ∥ Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X) ∥₂) ∥₂

        ≃⟨ Σ-cong-equiv-snd (λ s → ST.setTruncEquiv $ Σ-cong-equiv-snd λ g → Σ-cong-equiv-snd λ f → invEquiv P.equiv) ⟩

      Σ[ s ∈ S ] ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] Σ[ f ∈ (⟨ P s g ⟩ → T) ] ∥ ((p : ⟨ P s g ⟩) → Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X)) ∥₂ ∥₂

        ≃⟨ Σ-cong-equiv-snd (λ s → ST.setTruncEquiv $ Σ-cong-equiv-snd λ g → invEquiv (ST.setTruncateFstΣ≃ (isSet→ is-set-T))) ⟩

      Σ[ s ∈ S ] ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] ∥ Σ[ f ∈ (⟨ P s g ⟩ → T) ] ((p : ⟨ P s g ⟩) → Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X)) ∥₂ ∥₂

        ≃⟨ Σ-cong-equiv-snd (λ s → invEquiv ST.setTruncateSndΣ≃) ⟩

      Σ[ s ∈ S ] ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] Σ[ f ∈ (⟨ P s g ⟩ → T) ] ((p : ⟨ P s g ⟩) → Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X)) ∥₂

        ≃⟨ Σ-cong-equiv-snd (λ s → ST.setTruncEquiv $ Σ-cong-equiv-snd λ g → Σ-cong-equiv-snd λ f → goal s g f) ⟩

      Σ[ s ∈ S ] ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] Σ[ f ∈ (⟨ P s g ⟩ → T) ] Σ[ gr ∈ ⟨ Gr (s , ST.∣ g , f ∣₂) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X) ∥₂

        ≃⟨ Σ-cong-equiv-snd (λ s → ST.setTruncEquiv $ invEquiv Σ-assoc-≃) ⟩

      Σ[ s ∈ S ] ∥ Σ[ (g , f) ∈ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ] Σ[ gr ∈ ⟨ Gr (s , ST.∣ g , f ∣₂) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X) ∥₂

        ≃⟨ Σ-cong-equiv-snd (λ s → invEquiv ST.setTruncateUnwrapFstΣ≃) ⟩

      Σ[ s ∈ S ] ∥ Σ[ x ∈ ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂ ] Σ[ gr ∈ ⟨ Gr (s , x) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X) ∥₂

        ≃⟨ Σ-cong-equiv-snd (λ s → ST.setTruncateSndΣ≃) ⟩

      Σ[ s ∈ S ] ∥ Σ[ x ∈ ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂ ] ∥ Σ[ gr ∈ ⟨ Gr (s , x) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X) ∥₂ ∥₂

        ≃⟨ Σ-cong-equiv-snd (λ s → ST.setTruncIdempotent≃ (isSetΣ ST.isSetSetTrunc (λ _ → ST.isSetSetTrunc))) ⟩

      Σ[ s ∈ S ] Σ[ x ∈ ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂ ] ∥ Σ[ gr ∈ ⟨ Gr (s , x) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X) ∥₂

        ≃⟨ invEquiv Σ-assoc-≃ ⟩

      Σ[ sh ∈ Sh ] ∥ Σ[ gr ∈ ⟨ Gr sh ⟩ᵗ ] (⟨ Ps sh gr ⟩ → X) ∥₂

        ≃∎
        where module _ (s : S) where
          tangle' :
            ∀ (g : ⟨ G s ⟩ᵗ)
            → (f : ⟨ P s g ⟩ → T)
            → (h : (p : ⟨ P s g ⟩) → ⟨ H (f p) ⟩ᵗ)
            → (x : ∀ p → ⟨ Q (f p) (h p) ⟩ → X)
              →
            Σ[ x ∈ ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂ ] ∥ Σ[ gr ∈ ⟨ Gr (s , x) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X) ∥₂
          tangle' g f h x .fst = {! !}
          tangle' g f h x .snd = {! !}

          tangle* :
            ∀ (g : ⟨ G s ⟩ᵗ)
            → (f : ⟨ P s g ⟩ → T)
            → (h : (p : ⟨ P s g ⟩) → ⟨ H (f p) ⟩ᵗ)
            → (x : ∀ p → ⟨ Q (f p) (h p) ⟩ → X)
              →
            Σ[ x ∈ ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂ ] ∥ Σ[ gr ∈ ⟨ Gr (s , x) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X) ∥₂
          tangle* g f h x .fst = ST.∣ g , f ∣₂
          tangle* g f h x .snd = ST.∣ gr , ff ∣₂ where

            p? : T → ℙ ⟨ P s g ⟩
            p? t p .fst = ∃[ γ ∈ g ≡ g ] f (subst (λ - → ⟨ P s - ⟩) γ p) ≡ t
            p? t p .snd = isProp∃ _ _

            p?≃Fix : (t : T) (σ : G.pt₀ ≡ g)
              → {p : ⟨ P s g ⟩}
              → {p₀ : ⟨ P s G.pt₀ ⟩}
              → (π : PathP (λ i → ⟨ P s (σ i) ⟩) p₀ p)
              → ⟨ p? t p ⟩ ≃ ⟨ Fix* t (g , f) p₀ ⟩
            p?≃Fix t σ {p} {p₀} π =
              (∃[ γ ∈ g ≡ g ] f (γ ▷ p) ≡ t)
                ≃⟨ PT.propTrunc≃ $ Σ-cong-equiv (compPathlEquiv σ) (λ γ → compPathlEquiv $ cong f $ lemma γ) ⟩
              (∃[ γ ∈ G.pt₀ ≡ g ] f (γ ▷ p₀) ≡ t)
                ≃∎
                where abstract
                  lemma : (γ : g ≡ g) → (σ ∙ γ) ▷ p₀ ≡ γ ▷ p
                  lemma γ =
                    (σ ∙ γ) ▷ p₀ ≡⟨ substComposite (λ - → ⟨ P s - ⟩) σ γ p₀ ⟩
                    γ ▷ (σ ▷ p₀) ≡⟨ cong (γ ▷_) (fromPathP π) ⟩
                    γ ▷ p ∎

            f? : T → ℙ ⟨ P s g ⟩
            f? t p .fst = f p ≡ t
            f? t p .snd = is-set-T _ _

            f?→Fix : (t : T)
              → (γ : G.pt₀ ≡ g)
              → (p₀ : ⟨ P s G.pt₀ ⟩)
              → (p : ⟨ P s g ⟩)
              → (π : PathP (λ i → ⟨ P s (γ i) ⟩) p₀ p)
              → f p ≡ t
              → ∃[ γ ∈ G.pt₀ ≡ g ] f (γ ▷ p₀) ≡ t
            f?→Fix t γ p₀ p π fp≡t = ∃-intro γ $ cong f (fromPathP π) ∙ fp≡t

            Fix→f? : (t : T)
              → (γ : G.pt₀ ≡ g)
              → (p₀ : ⟨ P s G.pt₀ ⟩)
              → (p : ⟨ P s g ⟩)
              → (π : PathP (λ i → ⟨ P s (γ i) ⟩) p₀ p)
              → Σ[ γ ∈ G.pt₀ ≡ g ] f (γ ▷ p₀) ≡ t
              → f p ≡ t
            Fix→f? t γ p₀ p π (γ' , fγ'≡t) =
              cong f {! fromPathP π !} ∙ fγ'≡t

            bar : (t : T) → ∥ Path (Σ[ g ∈ ⟨ G s ⟩ᵗ ] ℙ ⟨ P s g ⟩) (g , f? t) (G.pt₀ , Fix* t (g , f)) ∥₁
            bar t = do
              pt₀≡g ← G.mere-path g
              pure $ ΣPathP (sym pt₀≡g , funExtNonDep λ σ → TypeOfHLevel≡ 1 $ ua $ {!f?≃Fix !})

            foo : (t : T) → ∥ Path (Σ[ g ∈ ⟨ G s ⟩ᵗ ] ℙ ⟨ P s g ⟩) (g , p? t) (G.pt₀ , Fix* t (g , f)) ∥₁
            foo t = do
              pt₀≡g ← G.mere-path g
              pure $ ΣPathP $
                sym pt₀≡g , ( funExtNonDep λ π → TypeOfHLevel≡ 1 $ ua $ p?≃Fix t pt₀≡g (symP π))

            gr : ⟨ Gr (s , ST.∣ g , f ∣₂) ⟩ᵗ
            gr .fst t .fst .fst .fst = g
            gr .fst t .fst .fst .snd = p? t
            gr .fst t .fst .snd = ST.merePath→pathSetTrunc (foo t)
            gr .fst t .snd .fst (p , ∃γ) = subst (λ - → ⟨ H - ⟩ᵗ) fp≡t (h p) where
              fp≡t : f p ≡ t
              fp≡t = PT.rec (is-set-T _ _) (λ { (γ , fγp≡t) → {!p!} }) ∃γ
            gr .fst t .snd .snd = ST.merePath→pathSetTrunc do
              h-paths ← P.choose₁ (H.mere-path ∘ h)
              pure $ funExt λ (p , ∃γ) → {!h-paths p  !}
            gr .snd = {! !}

            ff : ⟨ Ps (s , ST.∣ g , f ∣₂) gr ⟩ → X
            ff (t , (aut p , q)) = x p {!q!}

          tangle :
            ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] Σ[ f ∈ (⟨ P s g ⟩ → T) ] ((p : ⟨ P s g ⟩) → Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X)) ∥₂
              →
            Σ[ x ∈ ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂ ] ∥ Σ[ gr ∈ ⟨ Gr (s , x) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X) ∥₂
          tangle = ST.rec (isSetΣ ST.isSetSetTrunc (λ _ → ST.isSetSetTrunc)) λ (g , f , η) → tangle* g f (fst ∘ η) (snd ∘ η)

          untangle :
            ∀ (g : ⟨ G s ⟩ᵗ)
            → (f : ⟨ P s g ⟩ → T)
            → (gr  : ⟨ Gr (s , ST.∣ g , f ∣₂) ⟩ᵗ)
            → (ps : ⟨ Ps _ gr ⟩ → X)
            → Σ[ g ∈ ⟨ G s ⟩ᵗ ] Σ[ f ∈ (⟨ P s g ⟩ → T) ] ∥ ((p : ⟨ P s g ⟩) → Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X)) ∥₂
          untangle _ f (aut gr) ps = {!gr !}

          -- TODO: Maybe set-truncate the codomain of the LHS and the RHS
          module _ (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) where
            goaler-iso :
              Iso
                ((p : ⟨ P s g ⟩) → ∥ Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X) ∥₂)
                ∥ Σ[ gr ∈ ⟨ Gr (s , ST.∣ g , f ∣₂) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X) ∥₂
            goaler-iso .Iso.fun η = {! !}
            goaler-iso .Iso.inv = {! !}
            goaler-iso .Iso.rightInv = {! !}
            goaler-iso .Iso.leftInv = {! !}

            goal-iso :
              Iso
                ((p : ⟨ P s g ⟩) → Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X))
                (Σ[ gr ∈ ⟨ Gr (s , ST.∣ g , f ∣₂) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X))
            -- goal-iso .Iso.fun η .fst .fst t .fst .fst .fst = G.pt₀
            -- goal-iso .Iso.fun η .fst .fst t .fst .fst .snd = Fix* t (g , f)
            -- goal-iso .Iso.fun η .fst .fst t .fst .snd = refl
            -- goal-iso .Iso.fun η .fst .fst t .snd .fst = const H.pt₀
            goal-iso .Iso.fun η .fst .fst t .fst .fst .fst = g
            goal-iso .Iso.fun η .fst .fst t .fst .fst .snd p = (∃[ γ ∈ g ≡ g ] f (γ ▷ p) ≡ t) , isProp∃ _ _
            goal-iso .Iso.fun η .fst .fst t .fst .snd = ST.merePath→pathSetTrunc {! !}
            goal-iso .Iso.fun η .fst .fst t .snd .fst = uncurry λ p fix-p → subst (λ - → ⟨ H - ⟩ᵗ) (PT.rec ? ? fix-p) (η p .fst)
              -- PT.rec→Set {! !} (λ (γ , fγ≡t) → subst (λ - → ⟨ H - ⟩ᵗ) fγ≡t (η (γ ▷ p₀) .fst)) λ where
            -- --   (γ , γᴰ) (δ , δᴰ) → {! !}
            goal-iso .Iso.fun η .fst .fst t .snd .snd = {! !}
            goal-iso .Iso.fun η .fst .snd = {! !}
            goal-iso .Iso.fun η .snd (t , (p , fix*-p) , q) = η p .snd {!q!}
            goal-iso .Iso.inv (aut gr , x) p using (aut (g' , fix) , aut η) ← gr (f p) = η ({!p!} , {! !}) , x ∘ λ q → f p , ({!p!} , {! !}) , {! !}
            goal-iso .Iso.rightInv = {! !}
            goal-iso .Iso.leftInv = {! !}

            goal :
                ((p : ⟨ P s g ⟩) → Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X))
                  ≃
                (Σ[ gr ∈ ⟨ Gr (s , ST.∣ g , f ∣₂) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X))
            goal = isoToEquiv goal-iso
              -- .Iso.fun η → {! !}
              --   -- ( (λ t →
              --   --   ( (g , λ p → (f p ≡ t) , {! !}) , {! !})
              --   --   , (λ (p , fp≡t) → subst (λ - → ⟨ H - ⟩ᵗ) fp≡t (η p .fst)) , {! !})
              --   -- , {! !})
              --   -- , λ { (t , ((p , fp≡t) , q)) → η p .snd (transport (λ i → ⟨ Q (fp≡t (~ i)) (coe0→i (λ i → ⟨ H (fp≡t i) ⟩ᵗ) (~ i) (η p .fst)) ⟩) q) }
              -- .Iso.inv → {! !}
              -- .Iso.leftInv → {! !}
              -- .Iso.rightInv → {! !}
