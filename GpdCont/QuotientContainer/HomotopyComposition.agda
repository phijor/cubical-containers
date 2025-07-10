{-# OPTIONS --no-require-unique-meta-solutions #-}
open import GpdCont.Prelude

module GpdCont.QuotientContainer.HomotopyComposition (ℓ : Level) where

open import GpdCont.HomotopySet
open import GpdCont.HomotopyGroup.Base
open import GpdCont.HomotopyGroup.Action
open import GpdCont.HomotopyGroup.Subgroup
open import GpdCont.HomotopyGroup.Subaction
open import GpdCont.HomotopyGroup.Pi
open import GpdCont.HomotopyGroup.Stabilizer
open import GpdCont.HomotopyGroup.Wreath
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

  Whack* : (s : S) → (g : ⟨ G s ⟩ᵗ) → (f : ⟨ P s g ⟩ → T) → Subaction (ℓ-suc ℓ) ℓ (EnvGroup s) (envAction s)
  Whack* s g f = goal where
    goal : Subaction _ _ (EnvGroup s) (envAction s)
    goal .fst = ΠMono T (EnvGroupᴰ s) λ t → WrMonoSingle (G s) (P* s) (H t) $ StabMono (G s) (P* s) $ Fixed g f t
    goal .snd = {! !}

  Whack : (s : S) → Uᴰ s → Subaction (ℓ-suc ℓ) ℓ (EnvGroup s) (envAction s)
  Whack s = ST.rec (isSetSubaction (EnvGroup s) (envAction s)) $ uncurry (Whack* s)

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

  group-unit-left* : (s : S) (g : ⟨ G s ⟩ᵗ) (f : ⟨ P s g ⟩ → T) → hGroupEquiv (K (s , ST.∣ g , f ∣₂)) (G s)
  group-unit-left* s g f =
    ΠGroup T (Kᴰ (s , ST.∣ g , f ∣₂)) ≃ᴳ⟨ ΠGroupContractDomain T (Kᴰ (s , ST.∣ g , f ∣₂)) is-contr-T ⟩
    (Stab (G s) (P* s) (Fixed g f t₀) ≀[ StabAction (G s) (P* s) (Fixed g f t₀) ] H t₀) ≃ᴳ⟨ WrContractSnd (Stab (G s) (P* s) (Fixed g f t₀)) (StabAction (G s) (P* s) (Fixed g f t₀)) (H t₀) (is-triv-H t₀) ⟩
    (Stabℙ (G s) (P s) (Fixed g f t₀)) ≃ᴳ⟨ StabℙCongEquiv (G s) (P s) (Fixed g f t₀) (λ _ → ⊤) Fixed≡⊤ ⟩
    (Stabℙ (G s) (P s) (λ _ → ⊤)) ≃ᴳ⟨ StabℙAllEquiv (G s) (P s) ⟩
    (G s) ∎ᴳ
    where
      fix-all : ∀ p → ⟨ Fixed g f t₀ p ⟩
      fix-all p = do
        pt₀≡g ← G.mere-path s g
        return $ pt₀≡g , sym (is-contr-T .snd (f (subst (λ - → ⟨ P s - ⟩) pt₀≡g p)))

      Fixed≡⊤ : ∀ p → ⟨ Fixed g f t₀ p ⟩ ≡ Unit*
      Fixed≡⊤ p = isContr→≡Unit* $ inhProp→isContr (fix-all p) (str (Fixed g f t₀ p))

  group-unit-left : ∀ u → hGroupEquiv (K u) (G (u .fst))
  group-unit-left = uncurry λ s → ST.elim (λ uᴰ → isSetHGroupEquiv (K (s , uᴰ)) (G s)) (uncurry (group-unit-left* s))

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
  group-unit-right* s g f =
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
