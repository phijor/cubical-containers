{-# OPTIONS --lossy-unification #-}
module GpdCont.QuotientContainer.CompositionFixed where

open import GpdCont.Prelude
open import GpdCont.Prelude.Path
open import GpdCont.Prelude.Square
open import GpdCont.Equiv
open import GpdCont.Embedding
open import GpdCont.Univalence
open import GpdCont.HomotopySet
import      GpdCont.SetQuotients as SQ
import      GpdCont.Subuniverse
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Pi
open import GpdCont.GroupAction.Stabilizer using (module Setwise ; isPropIsStabilizer)
open import GpdCont.GroupAction.Equivariant
open import GpdCont.GroupAction.Faithful
open import GpdCont.Group.SymmetricGroup using (𝔖 ; symmConjGroupEquiv)
open import GpdCont.Group.Subgroup
open import GpdCont.Group.DirProd
open import GpdCont.Group.Pi using (ΠGroupEquiv)
open import GpdCont.Group.Opposite
open import GpdCont.Group.SemidirectProduct
open import GpdCont.Group.WreathProduct
open import GpdCont.Group.Equivs using (conjEquiv ; conjGroupEquiv)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (cong≃ ; isPointedTarget→isEquiv→isEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset as ℙ using (ℙ)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Foundations.Path as Path using (compPathlEquiv ; congPathIso ; isProp→isPropPathP)
open import Cubical.Functions.Logic as Logic using (hProp≡)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Functions.Fibration
import      Cubical.Data.Empty as Empty
import      Cubical.Data.Fin.Recursive as FinR
open import Cubical.Data.FinSet.Base as FinSet using (isFinOrd)
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
import      Cubical.Data.SumFin as Fin
open import Cubical.Data.Unit
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Pi
open import Cubical.Algebra.Group.GroupPath using (isGroupoidGroup ; uaGroup)
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_])
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

open Subgroup

private
  variable
    ℓ : Level
    A B C : Type ℓ

  Embedding→hSet : isSet A → Embedding A ℓ → hSet ℓ
  Embedding→hSet is-set-A (B , ι) .fst = B
  Embedding→hSet is-set-A (B , ι) .snd = Embedding-into-isSet→isSet ι is-set-A

  _↔_ : ∀ {ℓA ℓB} (A : Type ℓA) (B : Type ℓB) → Type _
  A ↔ B = (A → B) × (B → A)

  Fin : ℕ → hSet _
  Fin n .fst = Fin.Fin n
  Fin n .snd = Fin.isSetFin {n}

  sum : (n : ℕ) → (f : ⟨ Fin n ⟩ → ℕ) → ℕ
  sum zero f = 0
  sum (suc n) f = sum n (f ∘ Fin.fsuc) + f Fin.fzero

  ⊎-left-equiv : (A ≃ B) → (A ⊎ C) ≃ (B ⊎ C)
  ⊎-left-equiv e = isoToEquiv $ ⊎Iso (equivToIso e) idIso

  sum-Fin-equiv : ∀ {n} {f : ⟨ Fin n ⟩ → ℕ}
    → ⟨ Fin (sum n f) ⟩ ≃ (Σ[ k ∈ ⟨ Fin n ⟩ ] ⟨ Fin (f k) ⟩)
  sum-Fin-equiv {n = zero} {f} = Empty.uninhabEquiv (id _) (uncurry λ ())
  sum-Fin-equiv {n = suc n} {f} =
    ⟨ Fin (sum n (f ∘ Fin.fsuc) + (f Fin.fzero)) ⟩
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

  -- Idea: Do by injectivity of Fin and sum-Fin-equiv
  sum-permute-snd' : ∀ {n} (f f' : ⟨ Fin n ⟩ → ℕ)
    → (π : ⟨ Fin n ⟩ ≃ ⟨ Fin n ⟩)
    → (p : f ≡ f' ∘ equivFun π)
    → ⟨ Fin (sum n f) ⟩ ≃ ⟨ Fin (sum n f') ⟩
  sum-permute-snd' {n} f f' π p =
    ⟨ Fin (sum n f) ⟩
      ≃⟨ sum-Fin-equiv ⟩
    (Σ[ k ∈ ⟨ Fin n ⟩ ] ⟨ Fin (f k) ⟩ )
      ≃⟨ Σ-cong-equiv π (λ k → substEquiv (λ - → ⟨ Fin - ⟩) (p ≡$ k)) ⟩
    (Σ[ k ∈ ⟨ Fin n ⟩ ] ⟨ Fin (f' k) ⟩ )
      ≃⟨ invEquiv sum-Fin-equiv ⟩
    ⟨ Fin (sum n f') ⟩
      ≃∎

  -- isNonZero : ∀ {n} → ⟨ Fin n ⟩ → Type
  -- isNonZero {suc n} Fin.fzero = Empty.⊥
  -- isNonZero {suc n} (Fin.fsuc _) = Unit

  -- pred : ∀ {n} → Σ[ k ∈ ⟨ Fin (suc n) ⟩ ] isNonZero k → ⟨ Fin n ⟩
  -- pred (Fin.fsuc k , _) = k

  -- Fin-suc-cancel : ∀ {n m}
  --   → ⟨ Fin (suc n) ⟩ ≃ ⟨ Fin (suc m) ⟩
  --   → ⟨ Fin n ⟩ ≃ ⟨ Fin m ⟩
  -- Fin-suc-cancel {n} {m} = {! !}

  opaque
    Fin-inj : ∀ {n m} → ⟨ Fin n ⟩ ≃ ⟨ Fin m ⟩ → n ≡ m
    Fin-inj e = FinR.Fin-inj _ _ $ ua $ (invEquiv convert-equiv) ∙ₑ e ∙ₑ convert-equiv where
      to : ∀ {n} → ⟨ Fin n ⟩ → FinR.Fin n
      to {n = suc n} Fin.fzero = FinR.zero
      to {n = suc n} (Fin.fsuc k) = FinR.suc $ to k

      from : ∀ {n} → FinR.Fin n → ⟨ Fin n ⟩
      from {n = suc n} FinR.zero = Fin.fzero
      from {n = suc n} (FinR.suc k) = Fin.fsuc $ from k

      convert : ∀ {n} → Iso ⟨ Fin n ⟩ (FinR.Fin n)
      convert .Iso.fun = to
      convert .Iso.inv = from
      convert .Iso.sec = {! !}
      convert .Iso.ret = {! !}

      convert-equiv : ∀ {n} → ⟨ Fin n ⟩ ≃ (FinR.Fin n)
      convert-equiv = isoToEquiv convert

      convert-path : ∀ {n} → ⟨ Fin n ⟩ ≡ (FinR.Fin n)
      convert-path = isoToPath convert

  sum-permute-snd : ∀ {n} (f f' : ⟨ Fin n ⟩ → ℕ)
    → (π : ⟨ Fin n ⟩ ≃ ⟨ Fin n ⟩)
    → (p : f ≡ f' ∘ equivFun π)
    → sum n f ≡ sum n f'
  sum-permute-snd {n} f f' π p = Fin-inj $ sum-permute-snd' f f' π p

{-
  record Subaction (G : Group ℓ) (X : hSet ℓ) (σ : Action G X) (ℓH ℓY : Level) : Type (ℓ-max ℓ (ℓ-suc (ℓ-max ℓH ℓY))) where
    constructor mkSubaction
    field
      sub : Group ℓH
      sub-inc : isSubgroup G sub
      set : hSet ℓY
      act : Action sub set
      set-fun : ⟨ set ⟩ → ⟨ X ⟩
      set-fun-is-inc : isEmbedding set-fun
      -- is-equivariant : ∀ h → (act ⁺ h) ∘ set-fun ≡ set-fun ∘ (σ ⁺ isSubgroup.inc-fun sub-inc h)
      -- is-equivariant : (h : ⟨ sub ⟩) → (σ ⁺ isSubgroup.inc-fun sub-inc h) ∘ set-fun ≡ set-fun ∘ act ⁺ h

  module _ (G : Group ℓ) (X : hSet ℓ) (σ : Action G X) (ℓH ℓY : Level) where
    SubactionΣ : Type _
    SubactionΣ = Σ[ (H , _) ∈ Subgroup G ℓH ] Σ[ (Y , f) ∈ Embedding ⟨ X ⟩ ℓY ] Σ[ is-set-Y ∈ isSet Y ] Action H (Y , is-set-Y)

    isSetSubactionΣ : isSet SubactionΣ
    isSetSubactionΣ =
      isSetΣ isSetSubgroup λ where
        (H , _) → isSetΣ isSetEmbedding λ where
          (Y , f) → isSetΣ (isProp→isSet isPropIsSet) λ where
            is-set-Y → isSetAction

  isSetSubaction : ∀ {G : Group ℓ} {X : hSet ℓ} {σ : Action G X} {ℓH ℓY} → isSet (Subaction G X σ ℓH ℓY)
  isSetSubaction {G} {X} {σ} {ℓH} {ℓY} = isOfHLevelRespectEquiv 2 equiv $ isSetSubactionΣ G X σ ℓH ℓY where
    equiv : SubactionΣ G X σ ℓH ℓY ≃ Subaction G X σ ℓH ℓY
    equiv = strictEquiv
      (λ where
        ((H , ι) , (Y , f) , (is-set-Y , τ)) → mkSubaction H ι (Y , is-set-Y) τ (f .fst) (f .snd)
      )
      (λ where
        (mkSubaction H ι Y τ f is-emb-f) → (H , ι) , (⟨ Y ⟩ , (f , is-emb-f)) , str Y , τ
      )
  -}

  Ap : (X : hSet ℓ) → Action (𝔖 X) X
  Ap X .Action.action = id _
  Ap X .Action.pres· _ _ = refl

  _∼ˢᵘᵇ_ : {G : Group ℓ-zero} → (H₀ H₁ : Subgroup G ℓ-zero) → Type _
  H₀ ∼ˢᵘᵇ H₁ = GroupEquiv (H₀ .sub) (H₁ .sub)
  {-# INJECTIVE_FOR_INFERENCE _∼ˢᵘᵇ_ #-}

  Subgroup/ : (G : Group ℓ-zero) → Type _
  Subgroup/ G = (Subgroup G ℓ-zero) / _∼ˢᵘᵇ_


module _
  (S T : Type)
  (is-set-S : isSet S)
  (is-set-T : isSet T)
  (♯ᴾ : S → ℕ)
  (♯ꟴ : T → ℕ)
  (G : S → Group ℓ-zero)
  (σ : (s : S) → Action (G s) (Fin (♯ᴾ s)))
  (is-faithful-σ : ∀ s → isFaithful (σ s))
  (H : T → Group ℓ-zero)
  (τ : (t : T) → Action (H t) (Fin (♯ꟴ t)))
  (is-faithful-τ : ∀ t → isFaithful (τ t))
  -- (def : ∀ n → SQ.Definable (Subgroup (𝔖 (Fin n)) ℓ-zero) _∼ˢᵘᵇ_)
  (def : (X : hSet ℓ-zero) → isFinOrd ⟨ X ⟩ → SQ.Definable (Subgroup (𝔖 X) ℓ-zero) _∼ˢᵘᵇ_)
  where

  private
    P = Fin ∘ ♯ᴾ
    Q = Fin ∘ ♯ꟴ

  module σ {s} where
    open Action (σ s) public
    open ActionProperties (σ s) public

  module τ {t} where
    open Action (τ t) public
    open ActionProperties (τ t) public

  module G {s} = GroupStr (str (G s))
  module H {t} = GroupStr (str (H t))

  _≈_ : ∀ {s} → (f₀ f₁ : ⟨ P s ⟩ → T) → Type _
  f ≈ f' = Σ[ g ∈ ⟨ G _ ⟩ ] f ≡ f' ∘ (g σ.▷_)

  _∼_ : ∀ {s} → (f₀ f₁ : ⟨ P s ⟩ → T) → Type _
  f ∼ f' = ∥ f ≈ f' ∥₁

  Sh : Type _
  Sh = Σ[ s ∈ S ] ((⟨ P s ⟩ → T) / _∼_)

  module _ (s : S) where
    ♯* : (f : ⟨ P s ⟩ → T) → ℕ
    ♯* f = sum (♯ᴾ s) (♯ꟴ ∘ f)

    opaque
      ♯*-well-defined : (f f' : ⟨ P s ⟩ → T) → (g : ⟨ G s ⟩) → (f ≡ f' ∘ (g σ.▷_)) → ♯* f ≡ ♯* f'
      ♯*-well-defined f f' g p = sum-permute-snd (♯ꟴ ∘ f) (♯ꟴ ∘ f') (σ.action g) (cong (♯ꟴ ∘_) p)

  ♯ : Sh → ℕ
  ♯ = uncurry λ s → SQ.rec isSetℕ (♯* s) (λ f f' → ∃-rec (isSetℕ _ _) $ ♯*-well-defined s f f')

  Ps : Sh → hSet _
  Ps = Fin ∘ ♯

  module _ (s : S) (f : ⟨ P s ⟩ → T) where
    Ps* : hSet _
    Ps* .fst = Σ[ t ∈ T ] (fiber f t) × ⟨ Q t ⟩
    Ps* .snd = isSetΣ is-set-T λ t → isSet× (isSetΣSndProp (str $ P s) λ p → is-set-T (f p) t) (str $ Q t)

    Restrict : ⟨ G s ⟩ → Type _
    Restrict g = (t : T) (p : ⟨ P s ⟩) → (f p ≡ t) ≃ (f (g σ.▷ p) ≡ t)

    opaque
      isPropRestrict : ∀ g → isProp (Restrict g)
      isPropRestrict g = isPropΠ2 λ t p → isOfHLevel≃ 1 (is-set-T _ _) (is-set-T _ _)

      restrict-1g : Restrict G.1g
      restrict-1g t p = substEquiv (λ p' → f p' ≡ t) $ sym $ σ.action-1-id ≡$ p

      restrict-comp : ∀ {g h} → Restrict g → Restrict h → Restrict (g G.· h)
      restrict-comp {g} {h} rg rh t p =
        f p ≡ t
          ≃⟨ rg t p ⟩
        f (g σ.▷ p) ≡ t
          ≃⟨ rh t (g σ.▷ p) ⟩
        f (h σ.▷ (g σ.▷ p)) ≡ t
          ≃⟨ compPathlEquiv $ cong f (σ.action-comp-ext g h p) ⟩
        f ((g G.· h) σ.▷ p) ≡ t
          ≃∎

      restrict-inv : ∀ {g} → Restrict g → Restrict (G.inv g)
      restrict-inv {g} rg t p =
        f p ≡ t
          ≃⟨ compPathlEquiv $ cong f $ secEq (σ.action g) p ⟩
        f (g σ.▷ (g σ.▷⁻ p)) ≡ t
          ≃⟨ invEquiv $ rg t (g σ.▷⁻ p) ⟩
        f (g σ.▷⁻ p) ≡ t
          ≃⟨ compPathlEquiv $ cong f (σ.action-inv g ≡$ p) ⟩
        f (G.inv g σ.▷ p) ≡ t
          ≃∎

    G∣≤ : Subgroup (G s) _
    G∣≤ = isClosedSubset→Subgroup (G s) Restrict isPropRestrict restrict-1g restrict-comp restrict-inv

    G∣ : Group _
    G∣ = G∣≤ .sub

    module G∣ = GroupStr (str G∣)

    Fiber : T → hSet _
    Fiber t .fst = fiber f t
    Fiber t .snd = isSetΣSndProp (str $ P s) λ p → is-set-T (f p) t

    H∣ : Group _
    H∣ = ΠGroup {X = Σ[ t ∈ T ] fiber f t} λ (t , _) → H t

    σ∣ : ∀ t → Action G∣ (Fiber t)
    σ∣ t .Action.action (g , r) = Σ-cong-equiv (σ.action g) (r t)
    σ∣ t .Action.pres· (g , _) (h , _) = equivEq $ funExt λ (p , _) → Σ≡Prop (λ p → is-set-T (f p) t) $ σ.action-comp-ext g h p

    module σ∣ {t} where
      open Action (σ∣ t) public
      open ActionProperties (σ∣ t) public

    is-faithful-σ∣ : ∀ t → isFaithful (σ∣ t)
    is-faithful-σ∣ t {g = g₀ , r₀} {h = g₁ , r₁} htpy = Σ≡Prop isPropRestrict $ is-faithful-σ s $ {! htpy !}

    φ∣ : GroupHom (G∣ ᵒᵖ) (Aut H∣)
    φ∣ .fst g∣ .fst = equivΠDomain (Σ-cong-equiv-snd λ t → σ∣.action {t} g∣)
    φ∣ .fst g∣ .snd = makeIsGroupHom λ h₀ h₁ → refl
    φ∣ .snd = makeIsGroupHom λ g∣₀ g∣₁ → GroupEquiv≡ $ equivEq $ funExt₂ λ where
      h (t , p , fp≡t) → cong (λ - → h (t , -)) $ σ∣.action-comp-ext g∣₁ g∣₀ (p , fp≡t)

    -- Gr* : Group _
    -- Gr* = G∣ ⊗ H∣

    Gr* : Group _
    Gr* = SemidirProd H∣ G∣ φ∣

    ac* : Action Gr* Ps*
    ac* .Action.action (h , g∣) = equiv where
      equiv : ⟨ 𝔖 Ps* ⟩
      equiv = Σ-cong-equiv-snd λ t → Σ-cong-equiv (σ∣.action {t} g∣) λ fib → (τ.action (h (t , fib)))
    ac* .Action.pres· (h₀ , g∣₀) (h₁ , g∣₁) = equivEq $ funExt λ where
      (t , fib , q) → ΣPathP λ where
        .fst → refl′ t
        .snd → ΣPathP λ where
          .fst → σ∣.action-comp-ext g∣₀ g∣₁ fib
          .snd → τ.action-comp-ext (h₀ (t , fib)) (h₁ (t , g∣₀ σ∣.▷ fib)) q

    module ac* = Action ac*

    -- TODO: Define a version of this whose inverse computes a little better
    Ps-≃ : ⟨ Ps (s , [ f ]) ⟩ ≃ ⟨ Ps* ⟩
    Ps-≃ =
      ⟨ Fin (♯ (s , [ f ])) ⟩
        ≃⟨⟩
      ⟨ Fin $ sum (♯ᴾ s) (♯ꟴ ∘ f) ⟩
        ≃⟨ sum-Fin-equiv ⟩
      Σ[ p ∈ ⟨ Fin $ ♯ᴾ s ⟩ ] ⟨ Fin $ ♯ꟴ (f p) ⟩
        ≃⟨⟩
      Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩
        ≃⟨ Σ-cong-equiv-fst (totalEquiv f) ⟩
      Σ[ (t , _) ∈ Σ T (fiber f) ] ⟨ Q t ⟩
        ≃⟨ Σ-assoc-≃ ⟩
      Σ[ t ∈ T ] (fiber f t) × ⟨ Q t ⟩
        ≃∎

    π* : ⟨ Ps* ⟩ → ⟨ Ps (s , [ f ]) ⟩
    π* = invEq Ps-≃

    π' : ⟨ Ps* ⟩ → ⟨ Ps (s , [ f ]) ⟩
    π' (t , (p , fp≡t) , q) = invEq sum-Fin-equiv (p , subst (λ - → ⟨ Q - ⟩) (sym fp≡t) q)

    π*-β : π* ≡ π'
    π*-β = refl

    isFaithful-ac* : (∀ p → ⟨ Q (f p) ⟩) → isFaithful ac*
    isFaithful-ac* sec {g = h₀ , g∣₀} {h = h₁ , g∣₁} htpy = ΣPathP λ where
      .fst → funExt λ where
        (t , fib) → is-faithful-τ t $ equivExt λ where
          q → rectify {A = T} {B = λ t → ⟨ Q t ⟩} is-set-T (cong (snd ∘ snd) $ funExt⁻ (cong equivFun htpy) (t , fib , q))
      .snd → Σ≡Prop isPropRestrict $ is-faithful-σ s $ equivExt λ p → cong (fst ∘ fst ∘ snd) (funExt⁻ (cong equivFun htpy) (f p , (p , refl) , sec p))

    Gr*≤𝔖Ps* : Gr* ≤ 𝔖 Ps*
    Gr*≤𝔖Ps* = isFaithful→isSubgroup {σ = ac*} $ isFaithful-ac* {! !}

    Gr*≤𝔖Ps : Gr* ≤ 𝔖 (Ps (s , [ f ]))
    Gr*≤𝔖Ps = postCompEquiv→isSubgroup (symmConjGroupEquiv Ps* (Ps (s , [ f ])) $ invEquiv Ps-≃) Gr*≤𝔖Ps*

    sub* : Subgroup (𝔖 Ps*) ℓ-zero
    sub* .sub = Gr*
    sub* .is-sub = Gr*≤𝔖Ps*

    sub' : Subgroup (𝔖 (Ps (s , [ f ]))) ℓ-zero
    sub' .sub = Gr*
    sub' .is-sub = Gr*≤𝔖Ps

  {-
    sub* : Subaction (𝔖 (Ps (s , [ f ]))) (Ps (s , [ f ])) (Ap (Ps (s , [ f ]))) ℓ-zero ℓ-zero
    sub* .Subaction.sub = Gr*
    sub* .Subaction.sub-inc = Gr*≤𝔖Ps
    sub* .Subaction.set = Ps*
    sub* .Subaction.act = ac*
    sub* .Subaction.set-fun = π*
    sub* .Subaction.set-fun-is-inc = isEquiv→isEmbedding (equivIsEquiv $ invEquiv Ps-≃)

    sub'' : SubactionΣ (𝔖 Ps*) Ps* (Ap Ps*) ℓ-zero ℓ-zero
    sub'' .fst = Gr* , Gr*≤𝔖Ps*
    sub'' .snd .fst = ⟨ Ps* ⟩ , id↪ _
    sub'' .snd .snd .fst = str Ps*
    sub'' .snd .snd .snd = ac*

    sub'* : SubactionΣ (𝔖 (Ps (s , [ f ]))) (Ps (s , [ f ])) (Ap (Ps (s , [ f ]))) ℓ-zero ℓ-zero
    sub'* .fst = Gr* , Gr*≤𝔖Ps
    sub'* .snd .fst = ⟨ Ps* ⟩ , Equiv→Embedding (invEquiv Ps-≃)
    sub'* .snd .snd .fst = str Ps*
    sub'* .snd .snd .snd = ac*
  -}


  {-
  sub*-well-defined : ∀ s → (f f' : ⟨ P s ⟩ → T) → (g : ⟨ G s ⟩) → (f≡fσg : f ≡ f' ∘ (σ s ⁺ g))
    → PathP (λ i → let r = (s , SQ.eq/ _ _ ∣ g , f≡fσg ∣₁ i) in Subaction (𝔖 (Ps r)) (Ps r) (Ap (Ps r)) ℓ-zero ℓ-zero) (sub* s f) (sub* s f')
  sub*-well-defined s f f' f≡fσg = {! !}
  -}

  Ps-≃-extend : (sh : Sh) → ∃![ Ps' ∈ hSet ℓ-zero ] ⟨ Ps sh ⟩ ≃ ⟨ Ps' ⟩
  Ps-≃-extend = uncurry λ s → SQ.elimProp (λ f → isPropIsContr) goal where
    module _ {s} (f : ⟨ P s ⟩ → T) where
      exists : Σ[ Ps' ∈ hSet _ ] ⟨ Ps (s , [ f ]) ⟩ ≃ ⟨ Ps' ⟩
      exists .fst = Ps* s f
      exists .snd = Ps-≃ s f

      goal : ∃![ Ps' ∈ hSet _ ] ⟨ Ps (s , [ f ]) ⟩ ≃ ⟨ Ps' ⟩
      goal .fst = exists
      goal .snd (Y , e) = ΣPathP (ty-path , equiv-path) where
        ty-path : Ps* s f ≡ Y
        ty-path = hSet≡ $ ua $ invEquiv (Ps-≃ s f) ∙ₑ e

        equiv-path : PathP (λ i → ⟨ Ps (s , [ f ]) ⟩ ≃ ⟨ ty-path i ⟩) (Ps-≃ s f) e
        equiv-path = equivPathP $ →ua λ p →
            the
              (e .fst (invEq (Ps-≃ s f) (equivFun (Ps-≃ s f) p)) ≡ equivFun e p)
              (cong (equivFun e) (retEq (Ps-≃ s f) p))

  ↪Ps : (sh : Sh) → Embedding ⟨ Ps sh ⟩ _
  ↪Ps = uncurry λ s → SQ.elim (λ x → isSetEmbedding) (λ f → ⟨ Ps* s f ⟩ , Equiv→Embedding (invEquiv (Ps-≃ s f))) λ where
    f f' → ∃-elim {! !} λ where
      g f≡fσg → ΣPathP λ where
        .fst → ua (Σ-cong-equiv-snd λ t → Σ-cong-equiv-fst (Σ-cong-equiv (σ.action g) λ p → compPathlEquiv (sym (f≡fσg ≡$ p))))
        .snd → ΣPathP λ where
          .fst → ua→ $ funExt⁻ {! congPathIso {A = ?} ? .Iso.fun !}
          .snd → {! !}
          -- .fst → ua→ λ where
          --   (t , (p , fp≡t) , q) → the (PathP (λ i → ⟨ Fin (♯*-well-defined s f f' g f≡fσg i) ⟩) (π* s f (t , (p , fp≡t) , q)) (π* s f' (t , ((g σ.▷ p) , _) , q)))
          --     -- $ toPathP
          --     -- $ the (subst (λ - → ⟨ Fin - ⟩) (♯*-well-defined s f f' g f≡fσg) (π* s f (t , (p , fp≡t) , q)) ≡ π* s f' (t , ((g σ.▷ p) , _) , q))
          --     -- $ rectify {A = ℕ} {B = λ n → ⟨ Fin n ⟩} isSetℕ {p₀ = {! !}} {! !}
          --     $ congPathIso (λ i → {! (Ps-≃ s ?) !}) .Iso.inv {! !}
          -- .snd → {! !}

  Ps∞ : (sh : Sh) → singl (Ps sh)
  Ps∞ = uncurry λ s → SQ.elimProp (λ _ → isContr→isOfHLevel 1 (isContrSingl _)) (λ f → Ps* s f , hSet≡ (ua (Ps-≃ s f)))
  {-
  Ps∞ : (sh : Sh) → singl (Ps sh)
  Ps∞ = uncurry λ s → SQ.elim (λ _ → isContr→isOfHLevel 2 (isContrSingl _)) (λ f → Ps* s f , hSet≡ (ua (Ps-≃ s f))) λ where
      f f' → ∃-elim (λ _ → isProp→isPropPathP (λ i → isContr→isOfHLevel 1 (isContrSingl _)) _ _) λ where
        g f≡fσg → ΣPathP λ where
          .fst → hSet≡ $ ua $ Σ-cong-equiv-snd λ t → Σ-cong-equiv-fst (Σ-cong-equiv (σ.action g) (λ p → compPathlEquiv (sym (f≡fσg ≡$ p))))
          .snd → ΣSquarePProp {! !} $ goal f≡fσg where
    module _ {s} {f f' : ⟨ P s ⟩ → T} {g : ⟨ G s ⟩} (f≡fσg : f ≡ f' ∘ (σ s ⁺ g)) where
      goal : Square (ua (Ps-≃ s f)) (ua (Ps-≃ s f')) (λ i → ⟨ Fin (♯*-well-defined s f f' g f≡fσg i) ⟩) (ua $ Σ-cong-equiv-snd λ t → Σ-cong-equiv-fst (Σ-cong-equiv (σ.action g) (λ p → compPathlEquiv (sym (f≡fσg ≡$ p)))))
      goal = {! !}
        -- λ where
        --   i j → Glue ⟨ Ps* s f ⟩ {φ = ∂ i ∨ ∂ j} λ where
        --     (i = i0) → ua {! Ps-≃ !} j , {! !}
        --     (i = i1) → {! !}
        --     (j = i0) → {! !}
        --     (j = i1) → {! !}
  -}

  isSet↪Ps : ∀ sh → isSet (↪Ps sh .fst)
  isSet↪Ps = uncurry λ s → SQ.elimProp (λ _ → isPropIsSet) λ f → str (Ps* s f)

  Ps' : (sh : Sh) → hSet _
  -- Ps' sh = Ps-≃-extend sh .fst .fst
  Ps' sh = Ps∞ sh .fst

  isFinOrdPs' : (sh : Sh) → isFinOrd ⟨ Ps' sh ⟩
  isFinOrdPs' = uncurry λ s → SQ.elim (λ f → FinSet.isSetIsFinOrd) (λ f → ♯* s f , invEquiv (Ps-≃ s f)) (wd s) where
    wd' : (s : S) (f f' : ⟨ P s ⟩ → T) → (r : f ≈ f')
      → PathP (λ i → isFinOrd ⟨ Ps' (s , SQ.eq/ f f' ∣ r ∣₁ i) ⟩) (♯* s f , invEquiv (Ps-≃ s f)) (♯* s f' , invEquiv (Ps-≃ s f'))
    wd' s f f' (g , eq) = ΣPathP λ where
      .fst → ♯*-well-defined s f f' g eq
      .snd → equivPathP $ funExtNonDep λ {x₀} {x₁} p → {!Path.congPathEquiv !}

    wd : (s : S) (f f' : ⟨ P s ⟩ → T) → (r : f ∼ f')
      → PathP (λ i → isFinOrd ⟨ Ps' (s , SQ.eq/ f f' r i) ⟩) (♯* s f , invEquiv (Ps-≃ s f)) (♯* s f' , invEquiv (Ps-≃ s f'))
    wd s f f' = PT.elim {! !} $ wd' s f f'

  module _ s (f f' : ⟨ P s ⟩ → T) (g₀ : ⟨ G s ⟩) (f≡fσg : f ≡ f' ∘ (σ s ⁺ g₀)) where
    private
      f'≡fσg : f' ≡ f ∘ (σ s ⁻ g₀)
      f'≡fσg = σ.precomp-inv g₀ f≡fσg

    restrict-conj : ∀ h → Restrict s f h ≃ Restrict s f' (G.inv g₀ G.· (h G.· g₀))
    restrict-conj h = propBiimpl→Equiv (isPropRestrict _ _ _) (isPropRestrict _ _ _) to from
      where
        to : Restrict s f h → Restrict s f' (G.inv g₀ G.· (h G.· g₀))
        to r t p = compPathlEquiv $
          f' ((G.inv g₀ G.· (h G.· g₀)) σ.▷ p)
            ≡⟨ cong (λ - → f' (- σ.▷ p)) (G.·Assoc _ _ _) ⟩
          f' (((G.inv g₀ G.· h) G.· g₀) σ.▷ p)
            ≡⟨ cong f' (σ.action-comp-ext _ _ _) ⟩
          f' (g₀ σ.▷ ((G.inv g₀ G.· h) σ.▷ p))
            ≡⟨ sym (f≡fσg ≡$ _) ⟩
          f (((G.inv g₀ G.· h) σ.▷ p))
            ≡⟨ cong f (σ.action-comp-ext _ _ _) ⟩
          f (h σ.▷ (G.inv g₀ σ.▷ p))
            ≡⟨ sym (invEq (r _ (G.inv g₀ σ.▷ p)) refl) ⟩
          f (G.inv g₀ σ.▷ p)
            ≡⟨ cong f (σ.action-inv g₀ ≡$ p) ⟩
          f (g₀ σ.▷⁻ p)
            ≡⟨ sym (f'≡fσg ≡$ p) ⟩
          f' p
            ∎

        from : Restrict s f' (G.inv g₀ G.· h G.· g₀) → Restrict s f h
        from r t p = compPathlEquiv $
          f (h σ.▷ p)
            ≡⟨ f≡fσg ≡$ (h σ.▷ p) ⟩
          f' (g₀ σ.▷ (h σ.▷ p))
            ≡⟨ cong f' $ sym $ σ.action-comp-ext _ _ _ ⟩
          f' ((h G.· g₀) σ.▷ p)
            ≡⟨ cong (λ - → f' (- σ.▷ p)) $ sym $ cancel ⟩
          f' ((g₀ G.· (G.inv g₀ G.· (h G.· g₀))) σ.▷ p)
            ≡⟨ cong f' (σ.action-comp-ext _ _ _) ⟩
          f' ((G.inv g₀ G.· (h G.· g₀)) σ.▷ (g₀ σ.▷ p))
            ≡⟨ equivFun (r _ (g₀ σ.▷ p)) refl ⟩
          f' (g₀ σ.▷ p)
            ≡⟨ sym $ f≡fσg ≡$ p ⟩
          f p
            ∎
            where
              cancel : g₀ G.· (G.inv g₀ G.· (h G.· g₀)) ≡ (h G.· g₀)
              cancel = G.·Assoc g₀ (G.inv g₀) _ ∙ cong (G._· (h G.· g₀)) (G.·InvR g₀) ∙ G.·IdL _

    G∣-≃ : GroupEquiv (G∣ s f) (G∣ s f')
    G∣-≃ .fst = Σ-cong-equiv (conjEquiv (G s) g₀) restrict-conj
    G∣-≃ .snd = makeIsGroupHom λ _ _ → Σ≡Prop (isPropRestrict s f') (conjGroupEquiv (G s) g₀ .snd .IsGroupHom.pres· _ _)

    H∣-≃ : GroupEquiv (H∣ s f) (H∣ s f')
    H∣-≃ .fst = equivΠDomain (Σ-cong-equiv-snd λ t → Σ-cong-equiv (invEquiv $ σ.action g₀) λ p → compPathlEquiv $ sym $ f'≡fσg ≡$ p)
    H∣-≃ .snd = makeIsGroupHom λ _ _ → refl

    φ∣-coherence : ∀ h g →
      groupEquivFun H∣-≃ (groupEquivFun (φ∣ s f .fst g) h)
        ≡
      groupEquivFun (φ∣ s f' .fst (groupEquivFun G∣-≃ g)) (groupEquivFun H∣-≃ h)
    φ∣-coherence h (g , r') = funExt λ where
      (t , (p , fp≡t)) → cong h $ ΣPathP λ where
        .fst → refl′ t
        .snd → Σ≡Prop (λ p → is-set-T (f p) t) $
          g σ.▷ (g₀ σ.▷⁻ p)
            ≡⟨ cong (g σ.▷_) $ sym $ σ.action-inv g₀ ≡$ p ⟩
          g σ.▷ (G.inv g₀ σ.▷ p)
            ≡⟨ sym (σ.action-comp-ext _ _ p) ⟩
          (G.inv g₀ G.· g) σ.▷ p
            ≡⟨ sym (retEq (σ.action g₀) _) ⟩
          g₀ σ.▷⁻ (g₀ σ.▷ ((G.inv g₀ G.· g) σ.▷ p))
            ≡⟨ cong (g₀ σ.▷⁻_) $ sym $ σ.action-comp-ext _ _ _ ⟩
          g₀ σ.▷⁻ (((G.inv g₀ G.· g) G.· g₀) σ.▷ p)
            ≡⟨ cong (λ - → g₀ σ.▷⁻ (- σ.▷ p)) $ sym $ G.·Assoc _ _ _ ⟩
          g₀ σ.▷⁻ ((G.inv g₀ G.· (g G.· g₀)) σ.▷ p)
            ∎

    Gr*-≃ : GroupEquiv (Gr* s f) (Gr* s f')
    Gr*-≃ = SemidirectProductEquiv {N₀ = H∣ s f} {N₁ = H∣ s f'} (φ∣ s f) (φ∣ s f') H∣-≃ G∣-≃ φ∣-coherence

  Gr/ : (sh : Sh) → Subgroup/ (𝔖 (Ps' sh))
  Gr/ = uncurry λ s → SQ.elim {P = λ x → Subgroup/ (𝔖 (Ps' (s , x)))}
    (λ f → SQ.squash/) (Gr/* s) (wd s)
    module Gr/ where
      Gr/* : ∀ s (f : ⟨ P s ⟩ → T) → Subgroup/ (𝔖 (Ps* s f))
      Gr/* s f = [ sub* s f ]

      opaque
        α : ∀ s (f f' : ⟨ P s ⟩ → T) → (r : f ≈ f') → PathP (λ i → Subgroup/ (𝔖 (Ps' (s , SQ.eq/ f f' ∣ r ∣₁ i)))) (Gr/* s f) (Gr/* s f')
        α s f f' (g₀ , eq) = toPathP (SQ.eq/ _ (sub* s f') goal) where
          goal' : GroupEquiv (Gr* s f) (Gr* s f')
          goal' = Gr*-≃ s f f' g₀ eq

          goal : GroupEquiv (⟨ Gr* s f ⟩ , transport refl (str (Gr* s f))) (Gr* s f')
          goal = subst (λ - → GroupEquiv (⟨ Gr* s f ⟩ , -) (Gr* s f')) (sym (transportRefl (str (Gr* s f)))) goal'

        wd : ∀ s (f f' : ⟨ P s ⟩ → T)
          → (r : f ∼ f')
          → PathP (λ i → Subgroup/ (𝔖 (Ps' (s , SQ.eq/ f f' r i)))) (Gr/* s f) (Gr/* s f')
        wd s f f' = PT.elim (λ r → isOfHLevelPathP' 1 (SQ.squash/) _ _) (α s f f')

  Gr : (sh : Sh) → Subgroup (𝔖 (Ps' sh)) _
  Gr sh = SQ.Definable.emb (def (Ps' sh) (isFinOrdPs' sh)) $ Gr/ sh

  {-
    sub'-well-defined : PathP (λ i → let r = (s , SQ.eq/ _ _ ∣ g , f≡fσg ∣₁ i) in Subgroup (𝔖 (Ps r)) _) (sub' s f) (sub' s f')
    sub'-well-defined = ΣPathP λ where
        .fst → uaGroup Gr*-≃
        .snd → isSubgroupPathP'.isSubgroupPathP _ (Gr* s f) (Gr* s f') (Gr*≤𝔖Ps s f) (Gr*≤𝔖Ps s f') _ inc-path
      where
        sym-path : 𝔖 (Ps (s , [ f ])) ≡ 𝔖 (Ps (s , [ f' ]))
        sym-path i = 𝔖 (Ps (s , SQ.eq/ _ _ ∣ g , f≡fσg ∣₁ i))

        ⟨sym-path⟩ : ⟨ 𝔖 (Ps (s , [ f ])) ⟩ ≡ ⟨ 𝔖 (Ps (s , [ f' ])) ⟩
        ⟨sym-path⟩ = cong ⟨_⟩ sym-path

        inc-path : PathP (λ i → ⟨ uaGroup Gr*-≃ i ⟩ → ⟨sym-path⟩ i) (isSubgroup.inc-fun (Gr*≤𝔖Ps s f)) (isSubgroup.inc-fun (Gr*≤𝔖Ps s f'))
        inc-path = ua→ λ where
          (h∣ , g∣) → equivPathP $ funExtNonDep λ pp → toPathP {! !}

    sub*-well-defined : PathP (λ i → let r = (s , SQ.eq/ _ _ ∣ g , f≡fσg ∣₁ i) in Subgroup (𝔖 (Ps' r)) _) (sub* s f) (sub* s f')
    sub*-well-defined = ΣPathP λ where
        .fst → uaGroup Gr*-≃
        .snd → isSubgroupPathP'.isSubgroupPathP sym-path (Gr* s f) (Gr* s f') (Gr*≤𝔖Ps* s f) (Gr*≤𝔖Ps* s f') _ inc-path
      where
        sym-path : 𝔖 (Ps* s f) ≡ 𝔖 (Ps* s f')
        -- sym-path i = 𝔖 (hSet≡ (ua (Σ-cong-equiv-snd λ t → Σ-cong-equiv-fst (Σ-cong-equiv (σ.action g) (λ p → compPathlEquiv (sym (f≡fσg ≡$ p)))))) i)
        sym-path i = 𝔖 (Ps∞ (s , SQ.eq/ f f' ∣ g , f≡fσg ∣₁ i) .snd i)

        compute : (π : ⟨ 𝔖 (Ps* s f) ⟩) → (transport (λ i → ⟨ sym-path i ⟩) π) ≡ Σ-cong-equiv-snd {! !}
        compute π = {! !}

        inc-path' : (k : ⟨ Gr* s f ⟩) → PathP (λ i → ⟨ sym-path i ⟩) (ac*.action s f k) (ac*.action s f' (groupEquivFun Gr*-≃ k))
        inc-path' (h∣ , g∣) = toPathP $ equivExt λ where
          pq → {! !}

        inc-path : PathP (λ i → ⟨ uaGroup Gr*-≃ i ⟩ → ⟨ sym-path i ⟩) (Action.action $ ac* s f) (Action.action $ ac* s f')
        inc-path = ua→ inc-path'
 -}


    {-
    sub''-well-defined : PathP (λ i → let r = (s , SQ.eq/ _ _ ∣ g , f≡fσg ∣₁ i) in SubactionΣ (𝔖 (Ps' r)) (Ps' r) (Ap (Ps' r)) ℓ-zero ℓ-zero) (sub'' s f) (sub'' s f')
    sub''-well-defined = ΣPathP λ where
        .fst → subgroup-path
        .snd → {! !}
      where
        sym-path : 𝔖 (Ps* s f) ≡ 𝔖 (Ps* s f')
        sym-path = {! !}
        -- cong 𝔖 (? ∙ ?)
        --
        -- sym-path i₁ = 𝔖 (hcomp
        --   (λ i .o →
        --     (λ
        --       { (i₁ = i0) → GpdCont.QuotientContainer.CompositionFixed.goal f
        --       ; (i₁ = i1) → isPropIsContr (transport (λ z → ∃!-syntax (hSet ℓ-zero) (λ Ps'' → ⟨ Ps (s , _/_.eq/ f f' ∣ g , f≡fσg ∣₁ z) ⟩ ≃ ⟨ Ps'' ⟩)) (GpdCont.QuotientContainer.CompositionFixed.goal f)) (GpdCont.QuotientContainer.CompositionFixed.goal f') i
        --       }) _ .fst .fst .fst)
        --   (Σ-syntax T (λ t → fiber f t × ⟨ Q t ⟩)) , Ps' (s , _/_.eq/ f f' ∣ g , f≡fσg ∣₁ i) .snd)

        inc-path : PathP (λ i → ⟨ uaGroup Gr*-≃ i ⟩ → ⟨ sym-path i ⟩) (Action.action $ ac* s f) (Action.action $ ac* s f')
        inc-path = {! !}

        subgroup-path : PathP (λ i → Subgroup (𝔖 (Ps' (s , SQ.eq/ f f' ∣ g , f≡fσg ∣₁ i))) _) (Gr* s f , Gr*≤𝔖Ps* s f) (Gr* s f' , Gr*≤𝔖Ps* s f')
        subgroup-path = ΣPathP λ where
          .fst → uaGroup Gr*-≃
          .snd → isSubgroupPathP'.isSubgroupPathP sym-path (Gr* s f) (Gr* s f') (Gr*≤𝔖Ps* s f) (Gr*≤𝔖Ps* s f') _ inc-path

  sub' : (sh : Sh) → SubactionΣ (𝔖 (Ps' sh)) (Ps' sh) (Ap (Ps' sh)) ℓ-zero ℓ-zero
  sub' = uncurry λ s → SQ.elim (λ f → isSetSubactionΣ _ (Ps' (s , f)) (Ap (Ps' (s , f))) _ _)
    (sub'' s)
    (λ f f' → ∃-elim (λ r → isOfHLevelPathP' 1 (isSetSubactionΣ _ _ _ _ _) _ _) (sub''-well-defined s f f')) -- (sub*-well-defined s f f')
  -}

  {-
  sub'*-well-defined : ∀ s → (f f' : ⟨ P s ⟩ → T) → (g : ⟨ G s ⟩) → (f≡fσg : f ≡ f' ∘ (σ s ⁺ g))
    → PathP (λ i → let r = (s , SQ.eq/ _ _ ∣ g , f≡fσg ∣₁ i) in SubactionΣ (𝔖 (Ps r)) (Ps r) (Ap (Ps r)) ℓ-zero ℓ-zero) (sub'* s f) (sub'* s f')
  sub'*-well-defined s f f' g f≡fσg = ΣPathP λ where
      .fst → SubgroupPathP sym-path Gr*-path inc-path
      .snd → {! !}
    where
      sym-path : 𝔖 (Ps (s , [ f ])) ≡ 𝔖 (Ps (s , [ f' ]))
      sym-path i = 𝔖 (Fin (♯*-well-defined s f f' (∃-intro g f≡fσg) i))

      G∣-path : G∣ s f ≡ G∣ s f'
      G∣-path = {! !}

      Gr*-path : Gr* s f ≡ Gr* s f'
      Gr*-path = cong₂ _⊗_ G∣-path {! !}

      inc-path : PathP (λ i → ⟨ Gr*-path i ⟩ → ⟨ sym-path i ⟩) (isSubgroup.inc-fun (Gr*≤𝔖Ps s f)) (isSubgroup.inc-fun (Gr*≤𝔖Ps s f'))
      inc-path = funExtDep {! !}
  -}

  {-
  sub : (sh : Sh) → Subaction (𝔖 (Ps sh)) (Ps sh) (Ap (Ps sh)) ℓ-zero ℓ-zero
  sub = uncurry λ s → SQ.elim (λ f → isSetSubaction) (sub* s) λ f f' → ∃-elim (λ r → isOfHLevelPathP' 1 isSetSubaction _ _) (sub*-well-defined s f f')

  final-sub' : (sh : Sh) → Subgroup (𝔖 (Ps' sh)) ℓ-zero
  final-sub' = uncurry λ s → SQ.elim (λ f → isSetSubgroup) (sub* s) λ where
    f f' → ∃-elim (λ r → isOfHLevelPathP' 1 isSetSubgroup _ _) $ sub*-well-defined s f f'

  Gr≤𝔖Ps : (sh : Sh) → Subgroup (𝔖 (Ps sh)) ℓ-zero
  Gr≤𝔖Ps = uncurry λ s → SQ.elim {! !} {! !} {! !}
 -}
