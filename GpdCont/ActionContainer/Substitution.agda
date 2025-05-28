module GpdCont.ActionContainer.Substitution where

open import GpdCont.Prelude
open import GpdCont.HomotopySet
open import GpdCont.Univalence
open import GpdCont.GroupAction.Base

open import GpdCont.ActionContainer.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)
open import Cubical.HITs.SetQuotients as SQ using (_/_) hiding (module _/_)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)


private
  variable
    ℓ : Level

record StrictUniverse (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    is-U : hSet ℓ → hProp ℓ
    
  U : Type (ℓ-suc ℓ)
  U = ∥ Σ (hSet ℓ) (⟨_⟩ ∘ is-U) ∥₂

  field
    pt : U → Σ (hSet ℓ) (⟨_⟩ ∘ is-U)

  is-set-U : isSet U
  is-set-U = ST.isSetSetTrunc

  El : U → hSet ℓ
  El = fst ∘ pt

  uaᵁ : ∀ {A B : U} → ⟨ El A ⟩ ≡ ⟨ El B ⟩ → A ≡ B
  uaᵁ = {! !}

  Σᵁ : (A : U) (B : ⟨ El A ⟩ → U) → U
  Σᵁ = {! !}

  Σᵁ-≡ : {A A′ : U} {B : ⟨ El A ⟩ → U} {B′ : ⟨ El A′ ⟩ → U}
    → (p : A ≡ A′)
    → (q : PathP (λ i → ⟨ El (p i) ⟩ → U) B B′)
    → Σᵁ A B ≡ Σᵁ A′ B′
  Σᵁ-≡ = {! !}

module InUniverse (u : StrictUniverse ℓ) where
  open StrictUniverse u

  StrictActionContainer : Type (ℓ-suc ℓ)
  StrictActionContainer =
    Σ[ S ∈ hSet ℓ ]
    Σ[ P ∈ (⟨ S ⟩ → U) ]
    Σ[ G ∈ (⟨ S ⟩ → Group ℓ) ]
    ∀ s → Action (G s) (El (P s))

  -- [_∣_∼_] : (X : hSet ℓ) → {s : ⟨ S ⟩} → (v w : ⟨ El (P s) ⟩ → ⟨ X ⟩) → Type _

  ⟦_⟧ : (F : StrictActionContainer) → hSet ℓ → hSet ℓ
  ⟦ (S , P , G , σ) ⟧ X = ΣSet S Ext where

    _∼_ : ∀ {s} → (v w : ⟨ El (P s) ⟩ → ⟨ X ⟩) → Type _
    v ∼ w = ∃[ g ∈ ⟨ G _ ⟩ ] v ≡ w ∘ (σ _ ⁺ g)
    
    Ext : ⟨ S ⟩ → hSet _
    Ext s .fst = (⟨ El (P s) ⟩ → ⟨ X ⟩) / _∼_
    Ext s .snd = SQ.squash/

  Subst : (F G : StrictActionContainer) → StrictActionContainer
  Subst F@(S , P , G , σ) (T , Q , H , τ) = goal where
    module σ {s} where
      open Action (σ s) public
      open ActionProperties (σ s) public

    V : hSet ℓ
    V = ⟦ F ⟧ T

    R* : {s : ⟨ S ⟩} → (⟨ El (P s) ⟩ → ⟨ T ⟩) → U
    R* {s} v = Σᵁ (P s) (Q ∘ v)

    r-wd : ∀ (s : ⟨ S ⟩)
      → (v w : (⟨ El (P s) ⟩ → ⟨ T ⟩))
      → ∃[ g ∈ ⟨ G s ⟩ ] v ≡ w ∘ (σ _ ⁺ g)
      → R* v ≡ R* w
    r-wd s v w = ∃-rec (is-set-U _ _) λ g p → Σᵁ-≡ (uaᵁ (ua (σ.action g))) {! !}

    R : ⟨ V ⟩ → U
    R = uncurry λ s → SQ.rec is-set-U (R* {s}) (r-wd s)

    K : ⟨ V ⟩ → Group _
    K (s , f) = SQ.rec→Gpd.fun {! !} K* {! !} {! !} f where
      K* : (f : ⟨ El (P s) ⟩ → ⟨ T ⟩) → Group _
      K* f = ΠGroup (H ∘ f)

    goal : StrictActionContainer
    goal = V , R , {! !} , {! !}

  -- _[_] : (F G : ActionContainer ℓ) → ActionContainer ℓ
  -- F [ G ] = {! !} where
  --   module F = ActionContainer F
  --   module G = ActionContainer G

  --   U : hSet _
  --   U = {! !}

  --   F[G] : ActionContainer _
  --   F[G] .ActionContainer.Shape = {! !}
  --   F[G] .ActionContainer.Pos = {! !}
  --   F[G] .ActionContainer.Symm = {! !}
  --   F[G] .ActionContainer.action = {! !}
  --   F[G] .ActionContainer.is-set-shape = {! !}
  --   F[G] .ActionContainer.is-set-pos = {! !}
  --   F[G] .ActionContainer.symm-group-str = {! !}
  --   F[G] .ActionContainer.is-group-hom-action = {! !}

module FiniteContainer (ℓ : Level) where
  open import Cubical.Data.Nat
  open import Cubical.Data.SumFin
  open import Cubical.Data.Fin.LehmerCode
  open import Cubical.Algebra.Group.Subgroup
  open import Cubical.Algebra.SymmetricGroup using (Symmetric-Group)

  private
    Perm≃Lehmer : {k : ℕ} → (Fin k ≃ Fin k) ≃ LehmerCode k
    Perm≃Lehmer {k} = equivComp (SumFin≃Fin k) (SumFin≃Fin k) ∙ₑ lehmerEquiv

    Lehmer→Perm : {k : ℕ} → LehmerCode k → (Fin k ≃ Fin k)
    Lehmer→Perm = invEq Perm≃Lehmer

    totalSumLehmer : (k : ℕ) (f : Fin k → ℕ) (e : LehmerCode k)
      → totalSum f ≡ totalSum (f ∘ equivFun (Lehmer→Perm e))
    totalSumLehmer k f [] = refl
    totalSumLehmer k f (n ∷ e) = {! !}

    totalSumPermute : (k : ℕ) (f : Fin k → ℕ) (e : Fin k ≃ Fin k)
      → totalSum f ≡ totalSum (f ∘ equivFun e)
    totalSumPermute = {! !}
  

  U = ℕ

  is-set-U : isSet U
  is-set-U = isSetℕ

  El : U → hSet ℓ-zero
  El n .fst = Fin n
  El n .snd = isSetFin

  Σᵁ : (k : U) (f : ⟨ El k ⟩ → U) → U
  Σᵁ k f = totalSum {k} f

  syntax Σᵁ k (λ i → n) = Σᵁ[ i ≤ k ] n

  Σᵁ-equiv : {k : U} {f : ⟨ El k ⟩ → U} → ⟨ El (Σᵁ k f) ⟩ ≃ (Σ[ A ∈ ⟨ El k ⟩ ] ⟨ El (f A) ⟩)
  Σᵁ-equiv {k} {f} = invEquiv (SumFinΣ≃ k f)

  Σᵁ-permute : {k : U} {f : ⟨ El k ⟩ → U} (e : ⟨ El k ⟩ ≃ ⟨ El k ⟩) → (Σᵁ k f) ≡ (Σᵁ k (f ∘ equivFun e))
  Σᵁ-permute {k} {f} e = totalSumPermute k f e

  Σᵁ-elim : {k : U} {f : ⟨ El k ⟩ → U} → ⟨ El (Σᵁ k f) ⟩ → Σ[ A ∈ ⟨ El k ⟩ ] ⟨ El (f A) ⟩
  Σᵁ-elim = equivFun Σᵁ-equiv

  Sym : U → Group _
  Sym n = Symmetric-Group (Fin n) isSetFin

  Perm : U → Type _
  Perm n = Subgroup (Sym n)

  isSetPerm : (n : U) → isSet (Perm n)
  isSetPerm n = isSetSubgroup (Sym n)

  PermGroup : {n : U} → Perm n → Group _
  PermGroup {n} = Subgroup→Group (Sym n)

  record StrictActionContainer : Type (ℓ-suc ℓ) where
    field
      Shape : hSet ℓ
      ar : ⟨ Shape ⟩ → ℕ
      SubSymm : (s : ⟨ Shape ⟩) → Perm (ar s)

    Pos : ⟨ Shape ⟩ → hSet _
    Pos = El ∘ ar

    Symm : (s : ⟨ Shape ⟩) → Group _
    Symm = PermGroup ∘ SubSymm

    LabelEquiv : (X : Type ℓ) (s : ⟨ Shape ⟩) → (v w : ⟨ Pos s ⟩ → X) → Type _
    LabelEquiv X s v w = ∃[ (g , _) ∈ ⟨ Symm s ⟩ ] v ≡ w ∘ equivFun g

    _∼_ : {X : Type ℓ} {s : ⟨ Shape ⟩} → (v w : ⟨ Pos s ⟩ → X) → Type _
    _∼_ {X} {s} = LabelEquiv X s


  ⟦_⟧ : (F : StrictActionContainer) → hSet ℓ → hSet ℓ
  ⟦ F ⟧ X = ΣSet F.Shape Ext where
    module F = StrictActionContainer F

    Ext : ⟨ F.Shape ⟩ → hSet _
    Ext s .fst = (⟨ El (F.ar s) ⟩ → ⟨ X ⟩) / F.LabelEquiv ⟨ X ⟩ s
    Ext s .snd = SQ.squash/

  Subst : (F G : StrictActionContainer) → StrictActionContainer
  Subst F G = F[G] where
    module F = StrictActionContainer F
    module G = StrictActionContainer G

    V : hSet ℓ
    V = ⟦ F ⟧ G.Shape

    module Rep where
      ar* : (k : U) → (v : ⟨ El k ⟩ → ⟨ G.Shape ⟩) → U
      ar* k v = Σᵁ k (G.ar ∘ v)

      ar*-well-defined' : (k : U) (P : Perm k) (v w : ⟨ El k ⟩ → ⟨ G.Shape ⟩)
        → (g : ⟨ El k ⟩ ≃ ⟨ El k ⟩)
        → v ≡ w ∘ equivFun g
        → ar* k v ≡ ar* k w
      ar*-well-defined' k P v w g p = cong (ar* k) p ∙ sym (Σᵁ-permute g)

      ar*-well-defined : (k : U) (P : Perm k) (v w : ⟨ El k ⟩ → ⟨ G.Shape ⟩) → (∃[ (g , _) ∈ ⟨ PermGroup P ⟩ ] v ≡ w ∘ equivFun g) → ar* k v ≡ ar* k w
      ar*-well-defined k P v w = ∃-rec (is-set-U _ _) (λ g → ar*-well-defined' k P v w (g .fst))

    module _ (s : ⟨ F.Shape ⟩) where
      ar* : (v : ⟨ El (F.ar s) ⟩ → ⟨ G.Shape ⟩) → U
      ar* v = totalSum (G.ar ∘ v)

      ar*-well-defined : (v w : ⟨ El (F.ar s) ⟩ → ⟨ G.Shape ⟩) → v F.∼ w → ar* v ≡ ar* w
      ar*-well-defined v w = ∃-rec (is-set-U _ _) lemma where
        lemma : ((g , _) : ⟨ F.Symm s ⟩) → v ≡ w ∘ equivFun g → ar* v ≡ ar* w
        lemma (g , _) p = cong ar* p ∙ sym (totalSumPermute (F.ar s) (G.ar ∘ w) g)

    ar : ⟨ V ⟩ → U
    ar = uncurry λ s → SQ.rec is-set-U (ar* s) (ar*-well-defined s)

    K : (v : ⟨ V ⟩) → Perm (ar v)
    K = uncurry λ s → SQ.elim (λ f → isSetPerm (ar (s , f))) (K* s) {! !} where
      K* : ∀ s → (v : ⟨ El (F.ar s) ⟩ → ⟨ G.Shape ⟩) → Perm (ar* s v)
      K* s v .fst k .fst = Σ[ g ∈ ⟨ El (F.ar s) ⟩ ≃ ⟨ El (F.ar s) ⟩ ] {- Σ[ h ∈ ⟨ El (G.ar (v s)) ⟩ ≃ ⟨ El (G.ar (v s)) ⟩ ] -} {!Σ-cong-equiv g!} ≡ k
      K* s v .fst k .snd = {! !}
      K* s v .snd = {! !}

    F[G] : StrictActionContainer
    F[G] .StrictActionContainer.Shape = V
    F[G] .StrictActionContainer.ar = ar
    F[G] .StrictActionContainer.SubSymm = K

    -- module σ {s} where
    --   open Action (σ s) public
    --   open ActionProperties (σ s) public

    -- V : hSet ℓ
    -- V = ⟦ F ⟧ T

    -- R* : {s : ⟨ S ⟩} → (⟨ El (P s) ⟩ → ⟨ T ⟩) → U
    -- R* {s} v = Σᵁ (P s) (Q ∘ v)

    -- r-wd : ∀ (s : ⟨ S ⟩)
    --   → (v w : (⟨ El (P s) ⟩ → ⟨ T ⟩))
    --   → ∃[ g ∈ ⟨ G s ⟩ ] v ≡ w ∘ (σ _ ⁺ g)
    --   → R* v ≡ R* w
    -- r-wd s v w = ∃-rec (is-set-U _ _) λ g p → Σᵁ-≡ (uaᵁ (ua (σ.action g))) {! !}

    -- R : ⟨ V ⟩ → U
    -- R = uncurry λ s → SQ.rec is-set-U (R* {s}) (r-wd s)

    -- K : ⟨ V ⟩ → Group _
    -- K (s , f) = SQ.rec→Gpd.fun {! !} K* {! !} {! !} f where
    --   K* : (f : ⟨ El (P s) ⟩ → ⟨ T ⟩) → Group _
    --   K* f = ΠGroup (H ∘ f)

    -- goal : StrictActionContainer
    -- goal = V , R , {! !} , {! !}

module Test
  (P : hSet ℓ)
  (G : Group ℓ)
  (σ : Action G P)
  (is-ff-σ : ∀ π → isProp (fiber (σ ⁺_) π))
  (T : hSet ℓ)
  (Q : ⟨ T ⟩ → hSet ℓ)
  (H : ⟨ T ⟩ → Group ℓ)
  (τ : (t : ⟨ T ⟩) → Action (H t) (Q t))
  (X : hSet ℓ)
  where

  private
    module τ {t} = Action (τ t)
    module σ = Action σ

  σ[_∼_] : ∀ {Y : Type ℓ} (v w : ⟨ P ⟩ → Y) → Type _
  σ[_∼_] {Y} v w = ∃[ g ∈ ⟨ G ⟩ ] PathP (λ i → ua (σ.action g) i → Y) v w

  τ[_∣_∼_] : ∀ t → (v w : ⟨ Q t ⟩ → ⟨ X ⟩) → Type _
  τ[_∣_∼_] t v w = ∃[ h ∈ ⟨ H t ⟩ ] PathP (λ i → ua (τ.action h) i → ⟨ X ⟩) v w

  LHS : Type _
  LHS = (⟨ P ⟩ → Σ[ t ∈ ⟨ T ⟩ ] (⟨ Q t ⟩ → ⟨ X ⟩) / τ[ t ∣_∼_]) / σ[_∼_]

  RHS : Type _
  RHS = ?
