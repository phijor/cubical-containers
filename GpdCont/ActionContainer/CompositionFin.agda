{-# OPTIONS --lossy-unification #-}
open import GpdCont.Prelude hiding (_▷_)

module GpdCont.ActionContainer.CompositionFin (ℓ : Level) where

open import GpdCont.Prelude.Square
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
open import Cubical.Functions.Logic using (⊤ ; ⇔toPath)
open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import      Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
import      Cubical.Data.SumFin as Fin
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

private
  variable
    ℓ₀ : Level
    A B C : Type ℓ₀

  Fin : ℕ → hSet _
  Fin n .fst = Fin.Fin n
  Fin n .snd = Fin.isSetFin {n}

  sum : (n : ℕ) → (f : ⟨ Fin n ⟩ → ℕ) → ℕ
  sum zero f = 0
  sum (suc n) f = sum n (f ∘ Fin.fsuc) + f Fin.fzero

  sum-permute-snd : ∀ {n} (f : ⟨ Fin n ⟩ → ℕ)
    → (π : ⟨ Fin n ⟩ ≃ ⟨ Fin n ⟩)
    → sum n (f ∘ equivFun π) ≡ sum n f
  sum-permute-snd {(zero)} f π = refl
  sum-permute-snd {suc n} f π = {! !}

  ⊎-left-equiv : (A ≃ B) → (A ⊎ C) ≃ (B ⊎ C)
  ⊎-left-equiv e = isoToEquiv $ ⊎Iso (equivToIso e) idIso

  sum-Fin-equiv : ∀ {n} {f : ⟨ Fin n ⟩ → ℕ}
    → ⟨ Fin (sum n f) ⟩ ≃ (Σ[ k ∈ ⟨ Fin n ⟩ ] ⟨ Fin (f k) ⟩)
  sum-Fin-equiv {n = zero} {f} = Empty.uninhabEquiv (id _) (uncurry λ ())
  sum-Fin-equiv {n = suc n} {f} =
    ⟨ Fin (_ + _) ⟩
      ≃⟨ invEquiv (Fin.SumFin⊎≃ _ _) ⟩
    ⟨ Fin (sum n (f ∘ Fin.fsuc)) ⟩ ⊎ ⟨ Fin (f Fin.fzero) ⟩
      ≃⟨ ⊎-left-equiv (sum-Fin-equiv {n = n} {f = f ∘ Fin.fsuc}) ⟩
    (Σ[ k ∈ ⟨ Fin n ⟩ ] ⟨ Fin (f (inr k)) ⟩) ⊎ ⟨ Fin (f Fin.fzero) ⟩
      ≃⟨ ⊎-swap-≃ ⟩
    ⟨ Fin (f Fin.fzero) ⟩ ⊎ (Σ[ k ∈ ⟨ Fin n ⟩ ] ⟨ Fin (f (inr k)) ⟩)
      ≃⟨ ⊎-left-equiv $ invEquiv (Σ-contractFst isContrUnit) ⟩
    (Σ[ t ∈ Unit ] ⟨ Fin (f (inl t)) ⟩) ⊎ (Σ[ k ∈ ⟨ Fin n ⟩ ] ⟨ Fin (f (inr k)) ⟩)
      ≃⟨ invEquiv Σ⊎≃ ⟩
    (Σ[ k ∈ ⟨ Fin (suc n) ⟩ ] ⟨ Fin (f k) ⟩)
      ≃∎

module ComposeFix
  (S T : Type ℓ)
  (is-set-S : isSet S)
  (is-set-T : isSet T)
  (G : S → hGroup ℓ)
  (H : T → hGroup ℓ)
  (♯ᴾ : (s : S) → ⟨ G s ⟩ᵗ → ℕ)
  (♯ꟴ : (t : T) → ⟨ H t ⟩ᵗ → ℕ)
  where

  private
    module G {s} = hGroup (G s)
    module H {t} = hGroup (H t)

    P : (s : S) (g : ⟨ G s ⟩ᵗ) → hSet _
    P s g = Fin $ ♯ᴾ s g

    Q : (t : T) (h : ⟨ H t ⟩ᵗ) → hSet _
    Q t h = Fin $ ♯ꟴ t h

    _▷_ : ∀ {s} {g₀ g₁ : ⟨ G s ⟩ᵗ} → g₀ ≡ g₁ → ⟨ P s g₀ ⟩ → ⟨ P s g₁ ⟩
    γ ▷ p = subst (λ g → ⟨ P _ g ⟩) γ p

  module _ (s : S) where

  Shᴰ : S → Type ℓ
  Shᴰ s = ∥ Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T) ∥₂

  Sh : Type ℓ
  Sh = Σ S Shᴰ

{-
  Im : Sh → ℙ T
  Im = uncurry λ s → ST.rec isSetℙ λ where
    (g , f) t → (∃[ p ∈ ⟨ P s g ⟩ ] f p ≡ t) , isProp∃ _ _

  -- If P is finite, so is the image of functions ⟨ P s g ⟩ → T.
  -- Then we can apply (finite) choice
  G∣ : T → Sh → hGroup _
  G∣ t sh@(s , _) = FunGroup ⟨ Im sh t ⟩ (G s)

  P∣ : (t : T) (sh : Sh) → hAction _ (G∣ t sh)
  P∣ t sh@(s , _) = ΠActionΣ {! !} (λ _ → G s) (λ _ → P s)

  W : Sh → hGroup _
  W sh = ΠGroup T λ t → G∣ t sh

  module Fib (ord : ∀ {s} → Σ[ P₀ ∈ Type ℓ ] ∀ {g : ⟨ G s ⟩ᵗ} → ⟨ P s g ⟩ ≃ P₀) where
    lerp : ∀ {s} {g₀ g₁ : ⟨ G s ⟩ᵗ} → ⟨ P s g₀ ⟩ → ⟨ P s g₁ ⟩
    lerp {g₀} {g₁} = invEq (ord .snd) ∘ equivFun (ord .snd)

    Fib* : {s : S} (t : T) → (Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T)) → ℙ ⟨ P s G.pt₀ ⟩
    Fib* {(s)} t (g , f) p₀ .fst = f (lerp p₀) ≡ t
    Fib* {(s)} t (g , f) p₀ .snd = is-set-T _ _

    Fib : (t : T) (sh : Sh) → ℙ ⟨ P (sh .fst) G.pt₀ ⟩
    Fib t = uncurry λ s → ST.rec (isSet→ isSetHProp) $ Fib* t

    module UnitRight
      (is-contr-T : isContr T)
      where
      fib! : ∀ t sh p → ⟨ Fib t sh p ⟩
      fib! t = uncurry λ s → ST.elim (λ ∣f∣ → isSetΠ λ p → isProp→isSet (str (Fib t (s , ∣f∣) p))) λ where
        (g , f) p → isContr→isProp is-contr-T _ _

    module UnitLeft
      (is-contr-P : ∀ s g → isContr ⟨ P s g ⟩)
      where
      private
        p₀ : {s : S} {g : ⟨ G s ⟩ᵗ} → ⟨ P s g ⟩
        p₀ {s} {g} = is-contr-P s g .fst

      module _ (t : T) (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) (p : ⟨ P s G.pt₀ ⟩) where
        Fib-equiv* : (f p₀ ≡ t) ≃ (f (lerp p) ≡ t)
        Fib-equiv* = compPathlEquiv $ cong f $ sym (is-contr-P s g .snd (lerp p))

      -- Fib-equiv : ∀ t sh p → (f p₀ ≡ t) ≃ ⟨ Fib t sh p ⟩
      -- Fib-equiv t = uncurry λ s → ST.elim (λ ∣f∣ → isSetΠ λ p → isOfHLevel⁺≃ₗ 1 $ isProp→isSet $ is-set-T _ _) λ where
      --   (g , f) → {! Fib-equiv* t s g f !}


  -- The subset of positions (p₀ : P s pt₀) such that f p₀ ≡ t for any (f : ⟨ P s g ⟩ → T) , modulo transport.
  Fix* : {s : S} (t : T) → (Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T)) → ℙ ⟨ P s G.pt₀ ⟩
  Fix* t (g , f) p₀ .fst = (γ : G.pt₀ ≡ g) → f (γ ▷ p₀) ≡ t
  Fix* t (g , f) p₀ .snd = isPropΠ λ γ → is-set-T _ _

  Fix : (t : T) (sh : Sh) → ℙ ⟨ P (sh .fst) G.pt₀ ⟩
  Fix t = uncurry λ s → ST.rec (isSet→ isSetHProp) $ Fix* t

  Fixᴿ : {s : S} (t : T) → (g : ⟨ G s ⟩ᵗ) → (f : ⟨ P s g ⟩ → T) → ℙ ⟨ P s G.pt₀ ⟩
  Fixᴿ {s} t = G.elimSet' (λ g _ → isSetΠ λ f → isSetℙ) fix* coh* where
    fix* : (f : ⟨ P s G.pt₀ ⟩ → T) → ℙ ⟨ P s G.pt₀ ⟩
    fix* f p₀ .fst = f p₀ ≡ t
    fix* f p₀ .snd = is-set-T _ _

    coh* : ∀ g → (γ δ : G.pt₀ ≡ g) → subst (λ g → (⟨ P s g ⟩ → T) → ℙ ⟨ P s G.pt₀ ⟩) γ fix* ≡ subst (λ g → (⟨ P s g ⟩ → T) → ℙ ⟨ P s G.pt₀ ⟩) δ fix*
    coh* g γ δ = {! !}

    -- fix* : ∀ g → (γ : G.pt₀ ≡ g) → (f : ⟨ P s g ⟩ → T) → ℙ ⟨ P s G.pt₀ ⟩
    -- fix* g γ f p₀ .fst = f (γ ▷ p₀) ≡ t
    -- fix* g γ f p₀ .snd = is-set-T _ _

    -- coh* : ∀ g → (γ δ : G.pt₀ ≡ g) → fix* g γ ≡ fix* g δ
    -- coh* g γ δ = funExt λ f → funExt λ p₀ → ⇔toPath
    --   {! !}
    --   {! !}

  {-
  Subᴿ : (sh : Sh) (t : T) → Subgroup (ℓ-suc ℓ) (G (sh .fst))
  Subᴿ = uncurry λ s → ST.rec (isSet→ isSetSubgroup) $ uncurry $ G.elimSet (λ g _ → isSetΠ2 λ f t → isSetSubgroup) G∣ {! !}
    where module _ {s : S} where
      G∣ : (g : ⟨ G s ⟩ᵗ) (γ : G.pt₀ ≡ g) (f : ⟨ P s g ⟩ → T) (t : T) → Subgroup _ (G s)
      G∣ g γ f t .fst g' = {!g'!}
      G∣ g γ f t .snd = {! !}
  -}

  Subᴿ : (sh : Sh) (t : T) → Mono (ℓ-suc ℓ) (G (sh .fst))
  Subᴿ = uncurry λ s → ST.rec (isSet→ isSetMono) λ where
    (g , f) t .fst → Aut (∫ (G s) (ℙ* (G s) (P s))) (g , λ p → (f p ≡ t) , is-set-T _ _)
    (g , f) t .snd .hGroupMono.hom .hGroupHom.fun (aut (g' , _)) → g'
    (g , f) t .snd .hGroupMono.hom .hGroupHom.pres-pt₀ → G.elimSet {X = λ g → (f : ⟨ P s g ⟩ → T) (t : T) → g ≡ G.pt₀} (λ g _ → isSetΠ2 λ f t → G.is-groupoid _ _)
      (λ g γ f t → sym γ)
      (λ g γ δ → funExt₂ {! !})
      g f t
    (g , f) t .snd .hGroupMono.is-mono → {! !}

  GP∣* : {s : S} (t : T) → ((g , _) : Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T)) → Subaction _ ℓ (Aut G.asGroupoid g) (P s ∘ fst)
  GP∣* {s} t (g , f) .fst = StabMono' (G s) (ℙ* (G s) (P s)) g λ p → (f p ≡ t) , is-set-T _ _
  GP∣* {s} t (g , f) .snd .fst (aut (g' , fix)) = ΣSubSet (P s g') fix
  GP∣* {s} t (g , f) .snd .snd (aut (g' , fix)) = EmbeddingΣProp λ p → str (fix p)

  test : {s : S} (t : T) → ((g , _) : Σ[ g ∈ ⟨ G s ⟩ᵗ ] (⟨ P s g ⟩ → T)) → Subgroup (ℓ-suc ℓ) (Aut G.asGroupoid g)
  test {s} t (g , f) .fst (aut g') = ΣSubSet (P s g') λ (p' : ⟨ P s g' ⟩) → {!f!}
  test {s} t (g , f) .snd .fst = {! !}
  test {s} t (g , f) .snd .snd = {! !}

  G' : {s : S} (shᴰ : Shᴰ s) → Mono ℓ (G s)
  G' {s} = ST.rec isSetMono λ (g , _) → Aut G.asGroupoid g , record { hom = mkHGroupHom fst {! !} ; is-mono = {! !} }

  G~ : {s : S} (shᴰ : Shᴰ s) → hGroup ℓ
  G~ {s} = Mk ∘ ST.map fst where
    Mk : ∥ ⟨ G s ⟩ᵗ ∥₂ → hGroup ℓ
    Mk = ST.rec→Gpd.fun {! !} (Aut G.asGroupoid) λ where
      g₀ g₁ p q →
        the (cong (Aut (G.asGroupoid)) p ≡ cong (Aut (G.asGroupoid)) q) $ {!  !}

  GP∣ : T → ((s , shᴰ) : Sh) → Subaction (ℓ-suc ℓ) ℓ (G~ shᴰ) {! !}
  GP∣ t = uncurry λ s → ST.elim {B = λ shᴰ → Subaction (ℓ-suc ℓ) ℓ (G~ shᴰ) {! P s ∘ fst !}} {! !} (λ { (g , f) → GP∣* t (g , f) })

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
      (g , f) p γ → isContr→isProp is-contr-T (f (γ ▷ p)) t

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

        t₀≡f : t₀ ≡ f (is-contr-path-G .fst ▷ p)
        t₀≡f =
          t₀ ≡⟨ Sh-unit-left-β f ⟩
          f p₀ ≡⟨ cong f (is-contr-P _ _ .snd _) ⟩
          f (is-contr-path-G .fst ▷ p) ∎

      Fix-equiv* : (t₀ ≡ t) ≃ (∀ γ → f (γ ▷ p) ≡ t)
      Fix-equiv* =
        (t₀ ≡ t)
          ≃⟨ compPathlEquiv $ sym t₀≡f ⟩
        (f (is-contr-path-G .fst ▷ p) ≡ t)
          ≃⟨ invEquiv (Π-contractDom is-contr-path-G) ⟩
        (∀ γ → f (γ ▷ p) ≡ t)
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
        where module _ (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) where
          fwd :
            ((p : ⟨ P s g ⟩) → Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X))
              →
            (Σ[ gr ∈ ⟨ Gr (s , ST.∣ g , f ∣₂) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X))
          fwd η = gr , xs module fwd where
            open Restrict (s , ST.∣ g , f ∣₂)

            h : (p : ⟨ P s g ⟩) → ⟨ H (f p) ⟩ᵗ
            h = fst ∘ η

            x : (p : ⟨ P s g ⟩) → ⟨ Q (f p) (h p) ⟩ → X
            x = snd ∘ η

            Fix' : T → ℙ ⟨ P s g ⟩
            Fix' t p .fst = ∀ γ → f (γ ▷ p) ≡ t
            Fix' t p .snd = isPropΠ λ γ → is-set-T (f (γ ▷ p)) t

            h' : {t : T} → ((p , _) : Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ Fix' t p ⟩) → ⟨ H t ⟩ᵗ
            h' {t} (p , fix') = subst (λ - → ⟨ H - ⟩ᵗ) fp≡t (h p) module h' where
              fp≡t : f p ≡ t
              fp≡t = cong f (sym (transportRefl _)) ∙ fix' refl

            h'-filler : {t : T} (p : Σ[ p ∈ ⟨ P s g ⟩ ] ⟨ Fix' t p ⟩) → PathP (λ i → ⟨ H (h'.fp≡t (p .fst) (p .snd) i) ⟩ᵗ) (h (p .fst)) (h' p)
            h'-filler (p , fix') = subst-filler (λ - → ⟨ H - ⟩ᵗ) (h'.fp≡t _ _) (h p)

            fix-coh : {t : T} (γ : g ≡ G.pt₀)
              → {p₀ : ⟨ P s G.pt₀ ⟩}
              → {p : ⟨ P s g ⟩}
              → (π : PathP (λ i → ⟨ P s (γ i) ⟩) p p₀)
              → Fix' t p ≡ Fix t (s , ST.∣ g , f ∣₂) p₀
            fix-coh {t} γ {p₀} {p} π = ⇔toPath
              (λ where
                fix' γ' →
                  f (γ' ▷ p₀)
                    ≡[ i ]⟨ f (γ' ▷ fromPathP π (~ i)) ⟩
                  f (γ' ▷ (γ ▷ p))
                    ≡⟨ cong f $ sym (substComposite (λ - → ⟨ P s - ⟩) γ γ' p) ⟩
                  f ((γ ∙ γ') ▷ p)
                    ≡⟨ fix' (γ ∙ γ') ⟩
                  t ∎
              )
              (λ where
                fix γ' →
                  f (γ' ▷ p)
                    ≡[ i ]⟨ f (γ' ▷ fromPathP (symP π) (~ i)) ⟩
                  f (γ' ▷ (sym γ ▷ p₀))
                    ≡⟨ cong f $ sym (substComposite (λ - → ⟨ P s - ⟩) (sym γ) γ' p₀) ⟩
                  f ((sym γ ∙ γ') ▷ p₀)
                    ≡⟨ fix (sym γ ∙ γ') ⟩
                  t ∎
              )

            fixit : ∀ t (g≡pt₀ : g ≡ G.pt₀) → PathP (λ i → ℙ ⟨ P s (g≡pt₀ i) ⟩) (Fix' t) (Fix t (s , ST.∣ g , f ∣₂))
            fixit t g≡pt₀ = funExtNonDep (fix-coh g≡pt₀)

            merely-Fix : ∀ t → ∥ (g , Fix' t) ≡ (G.pt₀ , Fix* t (g , f)) ∥₁
            merely-Fix t = do
              g≡pt₀ ← PT.map sym $ G.mere-path g
              pure $ ΣPathP λ where
                .fst → g≡pt₀
                .snd → fixit t g≡pt₀

            grᴰ : ∀ t → ⟨ G∣f t ≀[ P∣f t ] H t ⟩ᵗ
            grᴰ t .fst .fst = (g , Fix' t)
            grᴰ t .fst .snd = merely-Fix t
            grᴰ t .snd .fst = h'
            grᴰ t .snd .snd = do
              pt₀≡h ← P.choose₁ (λ p → H.mere-path (h p))
              pure $ funExt λ where
                p*@(p , fix') →
                    h' p*
                      ≡⟨ sym (fromPathP (h'-filler p*)) ⟩
                    subst (λ - → ⟨ H - ⟩ᵗ) (h'.fp≡t p fix') (h p)
                      ≡⟨ cong (subst (λ - → ⟨ H - ⟩ᵗ) (h'.fp≡t p fix')) (sym (pt₀≡h p)) ⟩
                    subst (λ - → ⟨ H - ⟩ᵗ) (h'.fp≡t p fix') (H.pt₀ {t = f p})
                      ≡⟨ substCommSlice (λ - → ⟨ H - ⟩ᵗ) (λ - → ⟨ H - ⟩ᵗ) (λ t _ → H.pt₀ {t = t}) (h'.fp≡t p fix') (H.pt₀ {t = f p}) ⟩
                    H.pt₀ {t = t}
                      ∎

            gr : ⟨ Gr (s , ST.∣ g , f ∣₂) ⟩ᵗ
            gr .fst = grᴰ
            gr .snd = do
              g≡pt₀ ← PT.map sym $ G.mere-path g
              pure $ funExt λ t → ΣPathP (Σ≡Prop (λ _ → PT.isPropPropTrunc) (ΣPathP (g≡pt₀ , fixit t g≡pt₀)) , ΣPathP ({! !} , {! !}))

            xs : ⟨ Ps (s , ST.∣ g , f ∣₂) gr ⟩ → X
            xs (t , p*@(p , fix') , q) = x p q' where
              q' : ⟨ Q (f p) (η p .fst) ⟩
              q' = transport (λ i → ⟨ Q (h'.fp≡t _ _ (~ i)) (h'-filler p* (~ i)) ⟩) q

          bwd :
            (Σ[ gr ∈ ⟨ Gr (s , ST.∣ g , f ∣₂) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X))
              →
            ((p : ⟨ P s g ⟩) → Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X))
          bwd (gr*@(aut gr) , x) p using (g∣@(aut (g' , p?)) , aut η) ← gr (f p) = h , xs where
            open Restrict (s , ST.∣ g , f ∣₂)

            hmm* : ∥ ⟨ P∣f (f p) (hGroup.pt₀ (G∣f (f p))) ⟩ ∥₁
            hmm* = do
              g≡pt₀ ← PT.map sym $ G.mere-path g
              xx ← gr* .snd
              let yy = cong (fst ∘ fst ∘ fst) (xx ≡$ (f p))
              pure λ where
                .fst → g≡pt₀ ▷ p
                .snd → λ { γ → {! yy  !} }

            hmm : ∥ ⟨ P∣f (f p) g∣ ⟩ ∥₁
            hmm = hGroup.elimProp (G∣f (f p)) {P = λ g∣ → ∥ ⟨ P∣f (f p) g∣ ⟩ ∥₁} (λ _ → PT.isPropPropTrunc) hmm* g∣

            p∣ : ⟨ P∣f (f p) g∣ ⟩
            p∣ .fst = the ⟨ P s g' ⟩ $ transport {! !} p
            p∣ .snd = the ⟨ p? (p∣ .fst) ⟩ {! !}
            
            h : ⟨ H (f p) ⟩ᵗ
            h = η p∣

            ps : ⟨ Q (f p) h ⟩ → ⟨ Ps (s , ST.∣ g , f ∣₂) gr* ⟩
            ps q .fst = f p
            ps q .snd .fst = p∣
            ps q .snd .snd = q

            xs : ⟨ Q (f p) h ⟩ → X
            xs = x ∘ ps

          goal-iso :
            Iso
              ((p : ⟨ P s g ⟩) → Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X))
              (Σ[ gr ∈ ⟨ Gr (s , ST.∣ g , f ∣₂) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X))
          goal-iso .Iso.fun = fwd
          goal-iso .Iso.inv = bwd
          goal-iso .Iso.rightInv = {! !}
          goal-iso .Iso.leftInv = {! !}

          goal :
              ((p : ⟨ P s g ⟩) → Σ[ h ∈ ⟨ H (f p) ⟩ᵗ ] (⟨ Q (f p) h ⟩ → X))
                ≃
              (Σ[ gr ∈ ⟨ Gr (s , ST.∣ g , f ∣₂) ⟩ᵗ ] (⟨ Ps _ gr ⟩ → X))
          goal = isoToEquiv goal-iso
-}
