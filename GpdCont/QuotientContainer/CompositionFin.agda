{-# OPTIONS --lossy-unification #-}
module GpdCont.QuotientContainer.CompositionFin where

open import GpdCont.Prelude
open import GpdCont.Equiv
open import GpdCont.Embedding
open import GpdCont.Univalence
open import GpdCont.HomotopySet
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
open import GpdCont.Group.WreathProduct
open import GpdCont.Group.Equivs using (conjEquiv)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (cong≃ ; isPointedTarget→isEquiv→isEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset as ℙ using (ℙ)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Foundations.Path using (compPathlEquiv)
open import Cubical.Functions.Logic as Logic using (hProp≡)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Functions.Fibration
import      Cubical.Data.Empty as Empty
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

private
  variable
    ℓ : Level
    A B C : Type ℓ

  _↔_ : ∀ {ℓA ℓB} (A : Type ℓA) (B : Type ℓB) → Type _
  A ↔ B = (A → B) × (B → A)

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

  record Subaction (G : Group ℓ) (X : hSet ℓ) (σ : Action G X) (ℓH ℓY : Level) : Type (ℓ-suc (ℓMax ℓ ℓH ℓY)) where
    field
      sub : Group ℓH
      sub-inc : isSubgroup G sub
      set : hSet ℓY
      act : Action sub set
      set-fun : ⟨ set ⟩ → ⟨ X ⟩
      set-fun-is-inc : isEmbedding set-fun
      -- is-equivariant : ∀ h → (act ⁺ h) ∘ set-fun ≡ set-fun ∘ (σ ⁺ isSubgroup.inc-fun sub-inc h)
      is-equivariant : (h : ⟨ sub ⟩) → (σ ⁺ isSubgroup.inc-fun sub-inc h) ∘ set-fun ≡ set-fun ∘ act ⁺ h

  isSetSubaction : ∀ {G : Group ℓ} {X : hSet ℓ} {σ : Action G X} {ℓH ℓY} → isSet (Subaction G X σ ℓH ℓY)
  isSetSubaction = {! !}

  Ap : (X : hSet ℓ) → Action (𝔖 X) X
  Ap X .Action.action = id _
  Ap X .Action.pres· _ _ = refl

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
  where

  private
    P = Fin ∘ ♯ᴾ
    Q = Fin ∘ ♯ꟴ

  module σ {s} where
    open Action (σ s) public
    open ActionProperties (σ s) public
  module τ {t} = Action (τ t)
  module G {s} = GroupStr (str (G s))
  module H {t} = GroupStr (str (H t))

  _∼_ : ∀ {s} → (f₀ f₁ : ⟨ P s ⟩ → T) → Type _
  f ∼ f' = ∃[ g ∈ ⟨ G _ ⟩ ] f ≡ f' ∘ (g σ.▷_)

  Sh : Type _
  Sh = Σ[ s ∈ S ] ((⟨ P s ⟩ → T) / _∼_)

  module _ (s : S) where
    ♯* : (f : ⟨ P s ⟩ → T) → ℕ
    ♯* f = sum (♯ᴾ s) (♯ꟴ ∘ f)

    ♯*-well-defined : (f g : ⟨ P s ⟩ → T) → f ∼ g → ♯* f ≡ ♯* g
    ♯*-well-defined f g = ∃-rec (isSetℕ _ _) λ where
      gr p → subst (λ - → ♯* - ≡ ♯* g) (sym p) (sum-permute-snd (♯ꟴ ∘ g) (σ.action gr))

  ♯ : Sh → ℕ
  ♯ = uncurry λ s → SQ.rec isSetℕ (♯* s) (♯*-well-defined s)

  Ps : Sh → hSet _
  Ps = Fin ∘ ♯

  module _ (s : S) (f : ⟨ P s ⟩ → T) where
    module _ (t : T) where
      is-stab : ℙ ⟨ P s ⟩
      is-stab p .fst = f p ≡ t
      is-stab p .snd = is-set-T _ _

      open Setwise (G s) (P s) (σ s)

      G∣ = StabilizerGroup' is-stab

      isSubgroupGr : isSubgroup (G s) G∣
      isSubgroupGr = StabilizerSubroup' is-stab .snd

      P∣ : hSet _
      P∣ .fst = fiber f t
      P∣ .snd = isSetΣSndProp (str $ P s) λ p → is-set-T (f p) t

      σ∣ : Action G∣ P∣
      σ∣ = SubsetAction' is-stab

      Gr*ᴰ : Group _
      Gr*ᴰ = Wreath P∣ (H t) G∣ σ∣

      -- TODO: Maybe this should be on the outside: Πₜ ∥ Qₜ ∥₁ → (G∣ f)ₜ Wr Hₜ
      MG∣ : Group _
      MG∣ = ΠGroup {X = ∥ ⟨ Q t ⟩ ∥₁} $ const G∣

      MG∣≤G : MG∣ ≤ G s
      MG∣≤G .isSubgroup.inc .fst g = g {! !} .fst
      MG∣≤G .isSubgroup.inc .snd = {! !}
      MG∣≤G .isSubgroup.is-contr-ker-inc = {! !}

      MP∣ : hSet _
      MP∣ = (∥ ⟨ Q t ⟩ ∥₁ , isProp→isSet PT.isPropPropTrunc) ×Set P∣

      Mσ∣ : Action MG∣ MP∣
      Mσ∣ = ΠActionΣ (∥ ⟨ Q t ⟩ ∥₁ , isProp→isSet PT.isPropPropTrunc) (λ _ → P∣) (const σ∣)
      
      MGr*ᴰ : Group _
      MGr*ᴰ = Wreath MP∣ (H t) MG∣ Mσ∣

      isFaithful-Mσ∣ : isFaithful Mσ∣
      isFaithful-Mσ∣ = isFaithfulΠActionΣ (const σ∣) {! !}

      isFaithful-σ∣ : isFaithful σ∣
      isFaithful-σ∣ = {! !}

      {-
      υ*-sub : Subaction (G s) (P s) (σ s) _ _
      υ*-sub .Subaction.sub = G∣
      υ*-sub .Subaction.sub-inc = isSubgroupGr
      υ*-sub .Subaction.set = P∣
      υ*-sub .Subaction.act = σ∣
      υ*-sub .Subaction.set-fun = fst
      υ*-sub .Subaction.set-fun-is-inc _ _ = isEmbeddingFstΣProp (λ p → is-set-T _ _)
      υ*-sub .Subaction.is-equivariant _ = refl

      Gr*ᴰ-sub : Subaction (Wreath (P s) (H t) (G s) (σ s)) {! !} {! !} {! !} _
      Gr*ᴰ-sub .Subaction.sub = Gr*ᴰ
      Gr*ᴰ-sub .Subaction.sub-inc = goal where
        ι : ⟨ Gr*ᴰ ⟩ ↪ ⟨ Wreath (P s) (H t) (G s) (σ s) ⟩
        ι .fst (fib→H , g , g-stab) = {! !} , {! !}
        ι .snd = {! !}

        goal : Gr*ᴰ ≤ (Wreath (P s) (H t) (G s) (σ s))
        goal = Embedding→isSubgroup {! !} {! !}
      Gr*ᴰ-sub .Subaction.set = {! !}
      Gr*ᴰ-sub .Subaction.act = {! !}
      Gr*ᴰ-sub .Subaction.set-fun = {! !}
      Gr*ᴰ-sub .Subaction.set-fun-is-inc = {! !}
      Gr*ᴰ-sub .Subaction.is-equivariant = {! !}
      -}

    Gr* : Group _
    Gr* = ΠGroup {X = T} Gr*ᴰ

    Ps*ᴰ : T → hSet _
    Ps*ᴰ t = P∣ t ×Set (Q t)

    Ps* : hSet _
    Ps* = ΣSet (T , is-set-T) Ps*ᴰ

    ac*ᴰ : (t : T) → Action (Gr*ᴰ t) (Ps*ᴰ t)
    ac*ᴰ t = imprimitiveAction (P∣ t) (H t) (G∣ t) (σ∣ t) (τ t)

    MGr* : Group _
    MGr* = ΠGroup {X = T} MGr*ᴰ

    MPs*ᴰ : T → hSet _
    MPs*ᴰ t = MP∣ t ×Set (Q t)

    MPs* : hSet _
    MPs* = ΣSet (T , is-set-T) MPs*ᴰ

    Mac*ᴰ : (t : T) → Action (MGr*ᴰ t) (MPs*ᴰ t)
    Mac*ᴰ t = imprimitiveAction (MP∣ t) (H t) (MG∣ t) (Mσ∣ t) (τ t)

    isFaithful-ac*ᴰ : ∀ t → isFaithful (ac*ᴰ t)
    isFaithful-ac*ᴰ t {g = h₀ , g₀ , p₀} {h = h₁ , g₁ , p₁} htpy =
    --  ΣPathP λ where
    --   .fst → funExt λ { p∣ → is-faithful-τ t $ equivEq $ funExt λ q → cong snd $ cong equivFun htpy ≡$ (p∣ , q) }
    --   .snd → Σ≡Prop {! !} $ is-faithful-σ s $ equivEq $ funExt λ p → cong (fst ∘ fst) $ cong equivFun htpy ≡$ ((p , {! !}) , {! !})
      nonEmpty→isFaithfulImprimitiveAction (P∣ t) (H t) (G∣ t) (σ∣ t) (τ t) {! !} (is-faithful-τ t) {! !} {! !}

    isFaithful-Mac*ᴰ : ∀ t → isFaithful (Mac*ᴰ t)
    isFaithful-Mac*ᴰ t {g = h₀ , g∣₀} {h = h₁ , g∣₁} htpy = ΣPathP λ where
      .fst → funExt λ { p∣ → is-faithful-τ t $ equivEq $ funExt λ q → cong snd $ cong equivFun htpy ≡$ (p∣ , q) }
      .snd → funExt λ (∣q∣ : ∥ ⟨ Q t ⟩ ∥₁) → Σ≡Prop {! !} $ is-faithful-σ s $ equivEq $ funExt λ p∣ → PT.rec {! !} (λ q → cong (fst ∘ snd ∘ fst) $ cong equivFun htpy ≡$ ((∣q∣ , {!p∣!}) , q)) ∣q∣

    ac* : Action Gr* Ps*
    ac* = ΠActionΣ (T , is-set-T) Ps*ᴰ ac*ᴰ

    isFaithful-ac* : isFaithful ac*
    isFaithful-ac* = isFaithfulΠActionΣ ac*ᴰ isFaithful-ac*ᴰ

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

    ι*-hom : GroupHom Gr* (𝔖 Ps*)
    ι*-hom = Action→GroupHom ac*

    Gr*≤𝔖Ps* : Gr* ≤ 𝔖 Ps*
    Gr*≤𝔖Ps* = isFaithful→isSubgroup {σ = ac*} $ isFaithful-ac*

    Gr*≤𝔖Ps : Gr* ≤ 𝔖 (Ps (s , [ f ]))
    Gr*≤𝔖Ps = postCompEquiv→isSubgroup (symmConjGroupEquiv _ _ $ invEquiv Ps-≃) Gr*≤𝔖Ps*

    Gr*-sub : Subaction (𝔖 (Ps (s , [ f ]))) (Ps (s , [ f ])) (Ap (Ps (s , [ f ]))) ℓ-zero ℓ-zero
    Gr*-sub .Subaction.sub = Gr*
    Gr*-sub .Subaction.sub-inc = Gr*≤𝔖Ps
    Gr*-sub .Subaction.set = Ps*
    Gr*-sub .Subaction.act = ac*
    Gr*-sub .Subaction.set-fun = π*
    Gr*-sub .Subaction.set-fun-is-inc = isEquiv→isEmbedding (equivIsEquiv $ invEquiv Ps-≃)
    Gr*-sub .Subaction.is-equivariant = {! !}

  Gr*-sub-well-defined : ∀ s → (f f' : ⟨ P s ⟩ → T) → (g : ⟨ G s ⟩) → (f≡fσg : f ≡ f' ∘ (σ s ⁺ g))
    → PathP (λ i → let r = (s , SQ.eq/ _ _ ∣ g , f≡fσg ∣₁ i) in Subaction (𝔖 (Ps r)) (Ps r) (Ap (Ps r)) ℓ-zero ℓ-zero) (Gr*-sub s f) (Gr*-sub s f')
  Gr*-sub-well-defined s f f' f≡fσg = {! !}

  Gr-sub : (sh : Sh) → Subaction (𝔖 (Ps sh)) (Ps sh) (Ap (Ps sh)) ℓ-zero ℓ-zero
  Gr-sub = uncurry λ s → SQ.elim (λ f → isSetSubaction) (Gr*-sub s) λ f f' → ∃-elim {! !} (Gr*-sub-well-defined s f f')

  Gr : Sh → Group _
  Gr = Subaction.sub ∘ Gr-sub

  Ps' : Sh → hSet _
  Ps' = Subaction.set ∘ Gr-sub

  Ps-≃-Ps' : ∀ sh → ⟨ Ps sh ⟩ ≃ ⟨ Ps' sh ⟩
  Ps-≃-Ps' = uncurry λ s → SQ.elim (λ f → isOfHLevel≃ 2 (str $ Ps (s , f)) (str $ Ps' (s , f))) (Ps-≃ s) λ f f' → ∃-elim (λ _ → {! !}) λ where
    g f≡fσg → equivPathP $ funExtNonDep λ p → {! !}

  ac : (sh : Sh) → Action (Gr sh) (Ps' sh)
  ac = Subaction.act ∘ Gr-sub

{-

  Gr-sub : (sh : Sh) → Subaction (𝔖 (Ps sh)) (Ps sh) (Ap (Ps sh)) _ _
  Gr-sub = uncurry λ s → SQ.elim (λ _ → isSetSubaction) (Gr*-sub s) λ f₀ f₁ → ∃-elim (λ _ → isOfHLevelPathP' 1 isSetSubaction _ _) λ where
    g p i .Subaction.sub → {!p!}
    g p i .Subaction.sub-inc → {! !}
    g p i .Subaction.set → {! !}
    g p i .Subaction.act → {! !}
    g p i .Subaction.set-fun → {! !}
    g p i .Subaction.set-fun-is-inc → {! !}
    g p i .Subaction.is-equivariant → {! !}
-}

  {-
  module _ {s : S} where
    module _ (f : P' s → T) where
      Rᵁ : hSetSub
      Rᵁ = SubΣ (Representative (P s)) λ p' → Representative (Q (f p'))

      _ : ⟨ Rᵁ ⟩ ≡ (Σ[ p ∈ P' s ] Q' (f p))
      _ = refl

      r* : ⟨ 𝓤 ⟩
      r* = Σᵁ (code (P s)) λ p → code (Q (f p))

      r*-β : ⟨ El r* ⟩ ≃ ⟨ Rᵁ ⟩
      r*-β = pairᵁ _ _

    module _ (f₀ f₁ : P' s → T) (g : ⟨ G s ⟩) (rel : f₀ ≡ f₁ ∘ (g σ.▷_)) where
      Rᵁ-equiv : (Σ[ p ∈ P' s ] Q' (f₀ p)) ≃ (Σ[ p ∈ P' s ] Q' (f₁ p))
      Rᵁ-equiv = Σ-cong-equiv (σ.action g) λ (p' : P' s) → substEquiv Q' (rel ≡$ p')

      Rᵁ-path : Rᵁ f₀ ≡ Rᵁ f₁
      Rᵁ-path = uaSub _ _ Rᵁ-equiv

      r*-equiv : ⟨ El (r* f₀) ⟩ ≃ ⟨ El (r* f₁) ⟩
      r*-equiv = r*-β f₀ ∙ₑ Rᵁ-equiv ∙ₑ invEquiv (r*-β f₁)

      r*-eq : r* f₀ ≡ r* f₁
      r*-eq = isInjectiveElTrunc (r* f₀) (r* f₁) PT.∣ r*-equiv ∣₁

  r : U → ⟨ 𝓤 ⟩
  r = uncurry λ s → SQ.rec (str 𝓤) r* λ f₀ f₁ → ∃-rec (str 𝓤 _ _) (r*-eq f₀ f₁)

  R : U → hSetSub
  R = inc ∘ r

  module _ {s : S} where
    module _ (f : P' s → T) where
      is-stab : (t : T) → ℙ (P' s)
      is-stab t p .fst = f p ≡ t
      is-stab t p .snd = is-set-T (f p) t

      is-stab-invr : ∀ g (p : P' s) → ⟨ is-stab (f p) (g σ.▷ (g σ.▷⁻ p)) ⟩
      is-stab-invr g p = cong f (secEq (σ.action g) p)

      is-stab-invl : ∀ g (p : P' s) → ⟨ is-stab (f p) (g σ.▷⁻ (g σ.▷ p)) ⟩
      is-stab-invl g p = cong f (retEq (σ.action g) p)

      stab→-equiv : ∀ g t → (∀ p → (f (g σ.▷ p) ≡ t → f p ≡ t)) ≃ (∀ p → f p ≡ t → (f (G.inv g σ.▷ p) ≡ t))
      stab→-equiv g t =
        propBiimpl→Equiv {! !} {! !}
          (λ mk p fp≡t → mk (G.inv g σ.▷ p) $
            let h : (g σ.▷ (G.inv g σ.▷ p)) ≡ p
                h = {! !}
            in
            f (g σ.▷ (G.inv g σ.▷ p)) ≡⟨ cong f h ⟩
            f p ≡⟨ fp≡t ⟩
            t ∎
          )
          (λ mk p fgp≡t →
            let lem : f (G.inv g σ.▷ (g σ.▷ p)) ≡ t
                lem = mk (g σ.▷ p) fgp≡t
                adj : p ≡ G.inv g σ.▷ (g σ.▷ p)
                adj = {! !}
            in
            f p ≡⟨ cong f adj ⟩
            f (G.inv g σ.▷ (g σ.▷ p)) ≡⟨ lem ⟩
            t ∎
          )

      module Stab where
        open Setwise (G s) ⟨ Representative (P s) ⟩ˢ (σ s) public

      module _ (t : T) where
        Kᵁᴰ : Group ℓ
        Kᵁᴰ = Wreath _ (H t) (Stab.StabilizerGroup' (is-stab t)) (Stab.SubsetAction' (is-stab t))

      Kᵁ : Group ℓ
      Kᵁ = ΠGroup Kᵁᴰ

      module Kᵁ = GroupStr (str Kᵁ)

      ⟨K⟩' : Type ℓ
      ⟨K⟩' = {! !}

      ⟨K⟩-equiv : ⟨ Kᵁ ⟩ ≃ ⟨K⟩'
      ⟨K⟩-equiv =
        ((t : T) → (fiber f t → ⟨ H t ⟩) × (Σ[ g ∈ ⟨ G s ⟩ ] ((p' : P' s) → ⟨ is-stab t (g σ.▷ p') Logic.⇔ is-stab t p' ⟩)))
          ≃⟨ {! !} ⟩
        ((t : T) → ((p : P' s) → f p ≡ t → ⟨ H t ⟩) × (Σ[ g ∈ ⟨ G s ⟩ ] ((p' : P' s) → ⟨ is-stab t (g σ.▷ p') Logic.⇔ is-stab t p' ⟩)))
          ≃⟨ {! !} ⟩
        (((t : T) → ((p : P' s) → f p ≡ t → ⟨ H t ⟩)) × ∀ t → (Σ[ g ∈ ⟨ G s ⟩ ] ((p' : P' s) → ⟨ is-stab t (g σ.▷ p') Logic.⇔ is-stab t p' ⟩)))
          ≃⟨ {! !} ⟩
        (((p : P' s) → ⟨ H (f p) ⟩) × ∀ (t : T) → (Σ[ g ∈ ⟨ G s ⟩ ] ((p' : P' s) → (f (g σ.▷ p') ≡ t) ↔ (f p' ≡ t))))
          ≃⟨ {! !} ⟩
        ⟨K⟩'
          ≃∎

      module _ (k : ⟨ Kᵁ ⟩) where
        adjust : (p : P' s) → ⟨ H (f p) ⟩ × (Σ[ g ∈ ⟨ G s ⟩ ] (f p ≡ f (g σ.▷ p)) × (f p ≡ f (g σ.▷⁻ p)))
        adjust p =
          let (h-fib , g , g-stab) = k (f p)
              h = h-fib (p , refl)
          in λ where
            .fst → h
            .snd .fst → g
            .snd .snd .fst → sym (g-stab p .snd (refl′ (f p)))
            .snd .snd .snd → sym (g-stab (g σ.▷⁻ p) .fst $ cong f (secEq (σ.action g) p))

        ι→ᴾ : P' s → P' s
        ι→ᴾ p = let (_ , g , _) = k (f p) in g σ.▷ p
        
        {-
        fiber-equivᴾ : ∀ p₁ → {! !} ≃ fiber ι→ᴾ p₁
        fiber-equivᴾ p₁ =
          {! !} ≃⟨ {! !} ⟩
          Σ[ p₀ ∈ P' s ] (adjust p₀ .snd .fst) σ.▷⁻ p₁ ≡ p₀ ≃⟨ {! !} ⟩
          Σ[ p₀ ∈ P' s ] p₀ ≡ (adjust p₀ .snd .fst) σ.▷⁻ p₁ ≃⟨ {! !} ⟩
          Σ[ p₀ ∈ P' s ] (k (f p₀)) .snd .fst σ.▷ p₀ ≡ p₁ ≃∎
        -}

        ι←ᴾ : P' s → P' s
        ι←ᴾ p = let (_ , g , _) = k (f p) in g σ.▷⁻ p

        ι→ᴾ-Iso : Iso _ _
        ι→ᴾ-Iso = λ where
          .Iso.fun → ι→ᴾ
          .Iso.inv → ι←ᴾ
          .Iso.rightInv p →
            let (_ , g , g-stab) = k (f p)
                (_ , g' , _) = k (f (g σ.▷⁻ p))
                foo : f (g σ.▷⁻ p) ≡ f p
                foo = g-stab (g σ.▷⁻ p) .fst (is-stab-invr g p)

                sanity : g' ≡ g
                sanity = cong (λ t → k t .snd .fst) foo
            in
            g' σ.▷ (g σ.▷⁻ p) ≡⟨ cong (σ._▷ (g σ.▷⁻ p)) sanity ⟩
            g σ.▷ (g σ.▷⁻ p) ≡⟨ secEq (σ.action g) p ⟩
            p ∎
          .Iso.leftInv p →
            let (_ , g , g-stab) = k (f p)
                (_ , g' , _) = k (f (g σ.▷ p))

                stab : f (g σ.▷ p) ≡ f p
                stab = g-stab p .snd refl

                sanity : g' ≡ g
                sanity = cong (λ t → k t .snd .fst) stab
            in
            g' σ.▷⁻ (g σ.▷ p) ≡⟨ cong (σ._▷⁻ (g σ.▷ p)) sanity ⟩
            g σ.▷⁻ (g σ.▷ p) ≡⟨ retEq (σ.action g) p ⟩
            p ∎

        ι→ꟴ : {p : P' s} → (q : Q' (f p)) → Q' (f (ι→ᴾ p))
        ι→ꟴ {p} q using (h , _ , adj , _) ← adjust p = subst Q' adj (h τ.▷ q)

        ι←ꟴ : {p : P' s} → Q' (f (ι→ᴾ p)) → Q' (f p)
        ι←ꟴ {p} q
          using (_ , _ , adj' , _) ← adjust p
          using (h , g , _ , adj) ← adjust (ι→ᴾ p)
          = subst Q' {!adj'!} (h τ.▷ q)

        ι→ : ⟨ Rᵁ f ⟩ → ⟨ Rᵁ f ⟩
        ι→ (p , q) .fst = ι→ᴾ p
        ι→ (p , q) .snd = ι→ꟴ q

        ι≃ᴾ : P' s ≃ P' s
        ι≃ᴾ = isoToEquiv ι→ᴾ-Iso

        ι≃ꟴ : (p : P' s) → Q' (f p) ≃ Q' (f (ι→ᴾ p))
        ι≃ꟴ p = ι→ꟴ , {! !}

        ι≃ : ⟨ Rᵁ f ⟩ ≃ ⟨ Rᵁ f ⟩
        ι≃ = Σ-cong-equiv ι≃ᴾ ι≃ꟴ

        {-
        fiber-equiv : (r : ⟨ Rᵁ f ⟩) → {! !} ≃ fiber ι→ r
        fiber-equiv (p₁ , q₁) =
          {! !} ≃⟨ {! !} ⟩
          Σ[ (p₀ , p) ∈ fiber ι→ᴾ p₁ ] Σ[ q₀ ∈ Q' (f p₀) ] PathP (λ i → Q' (f (p i))) (ι→ꟴ q₀) q₁ ≃⟨ {! !} ⟩
          Σ[ p₀ ∈ P' s ] Σ[ p ∈ ι→ᴾ p₀ ≡ p₁ ] Σ[ q₀ ∈ Q' (f p₀) ] PathP (λ i → Q' (f (p i))) (ι→ꟴ q₀) q₁ ≃⟨ {! !} ⟩
          Σ[ p₀ ∈ P' s ] Σ[ q₀ ∈ Q' (f p₀) ] Σ[ p ∈ ι→ᴾ p₀ ≡ p₁ ] PathP (λ i → Q' (f (p i))) (ι→ꟴ q₀) q₁ ≃⟨ {! !} ⟩
          Σ[ r ∈ ⟨ Rᵁ f ⟩ ] Σ[ p ∈ ι→ᴾ (r .fst) ≡ p₁ ] PathP (λ i → Q' (f (p i))) (ι→ꟴ (r .snd)) q₁ ≃⟨ {! !} ⟩
          Σ[ r ∈ ⟨ Rᵁ f ⟩ ] ι→ r ≡ (p₁ , q₁) ≃⟨⟩
          fiber ι→ (p₁ , q₁) ≃∎

        ι← : ⟨ Rᵁ f ⟩ → ⟨ Rᵁ f ⟩
        ι← (p , q) =
          let (h-fib , g , g-stab) = k (f p)
              h = h-fib (p , refl)

              foo : f (g σ.▷ (g σ.▷⁻ p)) ≡ f p
              foo = cong f (secEq (σ.action g) p)

              adj : f p ≡ f (g σ.▷⁻ p)
              adj = sym $ g-stab (g σ.▷⁻ p) .fst foo
              -- foo : f (g σ.▷ p) ≡ f p
              -- foo = g-stab p .snd refl

              -- adj : f p ≡ f (G.inv g σ.▷ p)
              -- adj =
              --   f p ≡[ i ]⟨ f (secEq (σ.action g) p (~ i)) ⟩
              --   f (g σ.▷ (g σ.▷⁻ p)) ≡[ i ]⟨ {! g-stab (g σ.▷ p) .snd !} ⟩
              --   f (g σ.▷⁻ p) ≡⟨ {! !} ⟩
              --   f (G.inv g σ.▷ p) ∎

          -- in ι→' p q (H.inv h) (G.inv g) adj
          in λ where
            .fst → g σ.▷⁻ p
            .snd → subst Q' adj (h τ.▷⁻ q)
      -}

      ι-pres· : (k k' : ⟨ Kᵁ ⟩) → ι≃ (k Kᵁ.· k') ≡ ι≃ k ∙ₑ ι≃ k'
      ι-pres· k k' = equivEq $ funExt λ where
        (p , q) →
          ι≃ (k Kᵁ.· k') .fst (p , q) ≡⟨⟩
          ι→ᴾ (k Kᵁ.· k') p , (ι→ꟴ _ q) ≡⟨ {! !} ⟩
          (ι≃ k ∙ₑ ι≃ k') .fst (p , q) ∎

      ι-hom : GroupHom Kᵁ (𝔖 ⟨ Rᵁ f ⟩ˢ)
      ι-hom .fst = ι≃
      ι-hom .snd = makeIsGroupHom ι-pres·

      hasPropFibers-ι : (e : ⟨ Rᵁ f ⟩ ≃ ⟨ Rᵁ f ⟩) → isProp (fiber ι≃ e)
      hasPropFibers-ι e = {! !} where
        fiber-equiv : (k' : ⟨ Kᵁ ⟩) → {! !} ≃ fiber ι≃ (ι≃ k')
        fiber-equiv k' =
          {! !} ≃⟨ {! !} ⟩
          Σ[ k ∈ ⟨ Kᵁ ⟩ ] (∀ (p : P' s) (q : Q' (f p)) → Σ[ r ∈ ι→ᴾ k p ≡ ι→ᴾ k' p ] PathP (λ i → Q' (f (r i))) (ι→ꟴ k q) (ι→ꟴ k' q)) ≃⟨ {!  !} ⟩
          Σ[ k ∈ ⟨ Kᵁ ⟩ ] (∀ (p : P' s) (q : Q' _) → ι→ k (p , q) ≡ ι→ k' (p , q)) ≃⟨ {! ι→ k !} ⟩
          Σ[ k ∈ ⟨ Kᵁ ⟩ ] (∀ r → ι→ k r ≡ ι→ k' r) ≃⟨ Σ-cong-equiv-snd (λ k → {! ι→ k !} ) ⟩
          Σ[ k ∈ ⟨ Kᵁ ⟩ ] ι→ k ≡ ι→ k' ≃⟨ Σ-cong-equiv-snd (λ k → equivPathEquiv (ι≃ k) _) ⟩
          Σ[ k ∈ ⟨ Kᵁ ⟩ ] ι≃ k ≡ ι≃ k' ≃⟨⟩
          fiber ι≃ (ι≃ k') ≃∎

      isInjective-ι : isInjective ι-hom
      isInjective-ι k ιk≡1 = goal where
        module have where
          lem : equivFun (ι≃ k) ≡ id _
          lem = cong fst ιk≡1

          lem' : (r : ⟨ Rᵁ f ⟩) → ι→ k r ≡ r
          lem' = lem ≡$_

          lem'' : (p : P' s) → (q : Q' (f p)) → Σ[ r ∈ ι→ᴾ k p ≡ p ] PathP (λ i → Q' (f (r i))) (ι→ꟴ k q) q
          lem'' p q .fst = cong fst $ lem' (p , q)
          lem'' p q .snd = cong snd $ lem' (p , q)

          transform : ((ι≃ k) ≡ idEquiv ⟨ Rᵁ f ⟩) ≃ {! !}
          transform =
            (ι≃ k ≡ idEquiv ⟨ Rᵁ f ⟩) ≃⟨ {! !} ⟩
            (equivFun (ι≃ k) ≡ id _) ≃⟨ {! !} ⟩
            (∀ r → ι→ k r ≡ r) ≃⟨ {! !} ⟩
            (∀ p (q : Q' (f p)) → ι→ k (p , q) ≡ (p , q)) ≃⟨ {! !} ⟩
            (∀ p (q : Q' (f p)) → Σ[ r ∈ ι→ᴾ k p ≡ p ] PathP (λ i → Q' (f (r i))) (ι→ꟴ k q) q) ≃⟨ {! !} ⟩
            -- (∀ p → Σ[ r ∈ (Q' (f p) → ι→ᴾ k p ≡ p) ] ∀ q → PathP (λ i → Q' (f (r q i))) (ι→ꟴ k q) q) ≃⟨ {! !} ⟩
            {! !} ≃∎
            where
              slorp : (p₀ p₁ : P' s) → (Q' (f p₀) → ι→ᴾ k p₀ ≡ p₁) ≃ (ι→ᴾ k p₀ ≡ p₁)
              slorp p₀ p₁ = propBiimpl→Equiv {! !} {! !}
                {! !}
                {! !}

              blob : ∀ p →
                ((q : Q' (f p)) → Σ[ r ∈ ι→ᴾ k p ≡ p ] PathP (λ i → Q' (f (r i))) (ι→ꟴ k q) q)
                  ≃
                (Σ[ r ∈ ι→ᴾ k p ≡ p ] ((q : Q' (f p)) → PathP (λ i → Q' (f (r i))) (ι→ꟴ k q) q))
              blob p = propBiimpl→Equiv {! !} {! !}
                (λ q → {! !} , {! !})
                {! !}


        goal : k ≡ Kᵁ.1g
        goal = funExt λ t → ΣPathP (funExt (λ (h : Σ[ p ∈ _ ] f p ≡ t) → {! !}) , {! !})

{--1
      ι : Kᵁ ≤ 𝔖 ⟨ Rᵁ f ⟩ˢ
      ι .isSubgroup.inc = ι-hom
      ι .isSubgroup.is-contr-ker-inc = {! !}

      Kᵁ≤ : Subgroup (𝔖 ⟨ Rᵁ f ⟩ˢ) ℓ
      Kᵁ≤ .fst = Kᵁ
      Kᵁ≤ .snd = ι

      mediate : GroupEquiv (𝔖 ⟨ Rᵁ f ⟩ˢ) (𝔖 ⟨ R (s , [ f ]) ⟩ˢ)
      mediate = symmConjGroupEquiv ⟨ Rᵁ f ⟩ˢ ⟨ R (s , [ f ]) ⟩ˢ $ invEquiv (r*-β f)

      K*≤ : Subgroup (𝔖 ⟨ R (s , [ f ]) ⟩ˢ) ℓ
      K*≤ = postCompEquiv→Subgroup mediate Kᵁ≤

    module _ (f₀ f₁ : P' s → T) (g : ⟨ G s ⟩) (rel : f₀ ≡ f₁ ∘ (g σ.▷_)) where
      Kᵁ-path : Kᵁ f₀ ≡ Kᵁ f₁
      Kᵁ-path = {! !}

      Kᵁᴰ-equiv : ∀ t → GroupEquiv (Kᵁᴰ f₀ t) (Kᵁᴰ f₁ t)
      Kᵁᴰ-equiv t = WreathEquiv
        {- The equivalence of the sets being acted on -}
        (the (fiber f₀ t ≃ fiber f₁ t) $ fiberEquiv (σ.action g) rel t)
        {- Equivalence of the left groups -}
        (idGroupEquiv {G = H t})
        {- Equivalence of the right groups -}
        (Stab.equivSubset→GroupEquiv' f₀ (is-stab f₀ t) (is-stab f₁ t) g {! !})
        λ where
          (g' , stab-g') → funExt λ where
            (p , p∈stab) → ΣPathP λ where
              .fst →
                let lem =
                      (σ _ ⁻ g') ∘ (σ _ ⁻ g) ≡⟨ {! !} ⟩
                      (σ _ ⁻ g) ∘ (σ _ ⁻ (G.inv g G.· g' G.· g)) ∎
                in lem ≡$ p
              .snd → {! !}

      Kᵁ-equiv : GroupEquiv (Kᵁ f₀) (Kᵁ f₁)
      Kᵁ-equiv = ΠGroupEquiv _ Kᵁᴰ-equiv

      Kᵁ≤-eq' : PathP (λ i → Subgroup (uaGroup (symmConjGroupEquiv ⟨ Rᵁ f₀ ⟩ˢ ⟨ Rᵁ f₁ ⟩ˢ (Rᵁ-equiv f₀ f₁ g rel)) i) ℓ) (Kᵁ≤ f₀) (Kᵁ≤ f₁)
      Kᵁ≤-eq' = GroupEquiv→SubgroupPathP _ _ Kᵁ-equiv λ where
        k → equivEq $ funExt λ where
         (p , q) → let (h-fib , g₀ , g-stab) = k (f₀ (g σ.▷⁻ p))
                       (_ , g₁ , g₁-stab) = k (f₁ p)
          in ΣPathP λ where
            .fst →
              (g σ.▷ (g₀ σ.▷ (g σ.▷⁻ p))) ≡⟨ {! !} ⟩
              (G.inv g G.· (g₁ G.· g)) σ.▷ p ∎
            .snd → {! !}

      Kᵁ≤-eq : PathP (λ i → Subgroup (𝔖 ⟨ Rᵁ-path f₀ f₁ g rel i ⟩ˢ) ℓ) (Kᵁ≤ f₀) (Kᵁ≤ f₁)
      Kᵁ≤-eq = {! !}

      K*≤-eq : PathP (λ i → Subgroup (𝔖 ⟨ R (s , SQ.eq/ f₀ f₁ (∃-intro g rel) i) ⟩ˢ) ℓ) (K*≤ f₀) (K*≤ f₁)
      K*≤-eq = SubgroupPathP (λ i → {!⟨ R (s , SQ.eq/ f₀ f₁ (∃-intro g rel) i) ⟩ !}) {! !} {! !}

  K : (u : U) → Subgroup (𝔖 ⟨ R u ⟩ˢ) ℓ
  K = uncurry λ s → SQ.elim (λ _ → isSetSubgroup) K*≤ λ f₀ f₁ → ∃-elim (λ rel → isOfHLevelPathP' 1 isSetSubgroup _ _) $ K*≤-eq f₀ f₁
1--}

{-
  -- Given `s : S` and `f : P s → T`, the setwise stabilizer is a subgroup of `G s`.
  -- If `f ∼ f'`, then f and f' induce the same stabilizer subgroup. This defines a subgroup
  --
  --    Kᴰₜₛ ≤ Gₛ
  --
  -- for each `t : T` and `s : S`.
  is-stab : (t : T) → {s : S} (f : ⟨ P s ⟩ → T) → ℙ ⟨ P s ⟩
  is-stab t f p .fst = f p ≡ t
  is-stab t f p .snd = is-set-T (f p) t

  is-stab' : (t : T) → {s : S} (f : ⟨ P s ⟩ → T) → ℙ ⟨ P s ⟩
  is-stab' t f p .fst = f p Eq.≡ t
  is-stab' t f p .snd = subst isProp Eq.PathPathEq (is-set-T (f p) t)

  module _ {s : S} (f f' : ⟨ P s ⟩ → T) {t : T} (g : ⟨ G s ⟩) (rel : f ≡ f' ∘ (g σ.▷_)) where
    is-stab-path : is-stab t f ≡ is-stab t f' ∘ (σ s ⁺ g)
    is-stab-path = ℙ.⊆-extensionality _ _ λ where
      .fst p fp≡t → sym (rel ≡$ p) ∙ fp≡t
      .snd p f'σp≡t → (rel ≡$ p) ∙ f'σp≡t

    is-stab-path' : is-stab' t f ≡ is-stab' t f' ∘ (σ s ⁺ g)
    is-stab-path' = ℙ.⊆-extensionality _ _ λ where
      .fst p Eq.refl → Eq.pathToEq (sym (rel ≡$ p))
      .snd p Eq.refl → Eq.pathToEq (rel ≡$ p)

  Kᴰ⊂ : T → ((s , _) : U) → Subgroup (G s) (ℓ-suc ℓ)
  Kᴰ⊂ t = uncurry λ s → SQ.rec isSetSubgroup (Kᴰ⊂* s) (well-defined s) where module _ (s : S) where
    module Stab where
      open Setwise (G s) ⟨ P s ⟩ˢ (σ s) public

    Kᴰ⊂* : (f : ⟨ P s ⟩ → T) → Subgroup _ _
    Kᴰ⊂* f = Stab.SetwiseStabilizerSubgroup (is-stab t f)

    module _ (f f' : ⟨ P s ⟩ → T) (g : ⟨ G s ⟩) (f≡f'g : f ≡ f' ∘ (g σ.▷_)) where
      -- XXX: This doesn't actually work.
      well-defined' : SubgroupPath (Kᴰ⊂* f) (Kᴰ⊂* f')
      well-defined' = Stab.equivSubset→SetwiseStabilizerSubgroupPath (is-stab t f) (is-stab t f') g $ is-stab-path f f' g f≡f'g

    well-defined : (f f' : ⟨ P s ⟩ → T) → f ∼ f' → Kᴰ⊂* f ≡ Kᴰ⊂* f'
    well-defined f f' = ∃-rec (isSetSubgroup _ _) λ g p → equivFun (SubgroupPathEquiv _ _) $ well-defined' f f' g p

  ∣Kᴰ∣ : T → U → ∥ Group (ℓ-suc ℓ) ∥₂
  ∣Kᴰ∣ t = uncurry λ s → SQ.rec ST.isSetSetTrunc (∣Kᴰ∣* s) (well-defined s) where module _ (s : S) where
    module Stab where
      open Setwise (G s) ⟨ P s ⟩ˢ (σ s) public

    Kᴰ* : (f : ⟨ P s ⟩ → T) → Group _
    Kᴰ* f = Stab.StabilizerGroup (is-stab t f)

    ∣Kᴰ∣* : (f : ⟨ P s ⟩ → T) → ∥ Group _ ∥₂
    ∣Kᴰ∣* f = ∣ Kᴰ* f ∣₂

    module _ (f f' : ⟨ P s ⟩ → T) (g : ⟨ G s ⟩) (f≡f'g : f ≡ f' ∘ (g σ.▷_)) where
      stab-path : Kᴰ* f ≡ Kᴰ* f'
      stab-path = Stab.equivSubset→GroupPath (is-stab t f) (is-stab t f') g $ is-stab-path f f' g f≡f'g

    well-defined : (f f' : ⟨ P s ⟩ → T) → f ∼ f' → ∣Kᴰ∣* f ≡ ∣Kᴰ∣* f'
    well-defined f f' = ∃-rec (ST.isSetSetTrunc _ _) λ g p → cong ∣_∣₂ $ stab-path f f' g p

  K*-Hasegawa : (s : S) → (f : ⟨ P s ⟩ → T) → Group (ℓ-suc ℓ)
  K*-Hasegawa s f = ΠGroup Inner where
    module Stab = Setwise (G s) ⟨ P s ⟩ˢ (σ s)

    Inner : (t : T) → Group _
    Inner t = Wreath _ (H t) (Stab.StabilizerGroup (is-stab t f)) (Stab.SubsetAction (is-stab t f))

  K*-Hasegawaᵝ : (s : S) → (f : ⟨ P s ⟩ → T)
    → ⟨ K*-Hasegawa s f ⟩ ≡ ((t : T) → (fiber f t → ⟨ H t ⟩) × (Σ[ g ∈ ⟨ G s ⟩ ] (is-stab t f ∘ (σ s ⁺ G.inv g) ≡ is-stab t f)))
  K*-Hasegawaᵝ s f = refl

  _ : (s : S) → (f : ⟨ P s ⟩ → T) → ∀ t g → ( ⟨_⟩ ∘ is-stab t f ∘ (σ s ⁺ G.inv g) ≡ ⟨_⟩ ∘ is-stab t f) ≡ (∀ p → (f (G.inv g σ.▷ p) ≡ t) ≡ (f p ≡ t))
  _ = λ s f t g → sym funExtPath

  -- _ : (s : S) → (f : ⟨ P s ⟩ → T) → ∀ t g → ( ⟨_⟩ ∘ is-stab t f ∘ (σ s ⁺ G.inv g) ≡ ⟨_⟩ ∘ is-stab t f) ≡ ({! !} ≡ fiber f t)
  -- _ = λ s f t g → refl
  --
  mediate : {s : S} → {f f' : ⟨ P s ⟩ → T}
    → (g₀ : ⟨ G s ⟩)
    → (f ≡ f' ∘ (σ s ⁺ g₀))
    → ⟨ K*-Hasegawa s f ⟩ ≃ ⟨ K*-Hasegawa s f' ⟩
  mediate {s} {f} {f'} g₀ rel = equivΠCod λ t → Σ-cong-equiv (equivΠDomain $ fiber-equiv t) (const $ tail-equiv t) where
    rel' : (f' ≡ f ∘ (σ s ⁻ g₀))
    rel' = σ.precomp-inv g₀ rel

    fiber-equiv : ∀ t → fiber f' t ≃ fiber f t
    fiber-equiv t = Σ-cong-equiv (invEquiv $ σ.action g₀) λ p →
      (f' p ≡ t) ≃⟨ substEquiv (_≡ t) (rel' ≡$ p) ⟩
      (f (σ  _ ⁻ g₀ $ p) ≡ t) ≃∎

    module Stab = Setwise (G s) ⟨ P s ⟩ˢ (σ s)

    tail-equiv : ∀ t →
      (Σ[ g ∈ ⟨ G s ⟩ ] (is-stab t f ∘ (σ s ⁺ G.inv g) ≡ is-stab t f))
        ≃
      (Σ[ g ∈ ⟨ G s ⟩ ] (is-stab t f' ∘ (σ s ⁺ G.inv g) ≡ is-stab t f'))
    tail-equiv t = Stab.equiv (is-stab t f) (is-stab t f') g₀ $ is-stab-path f f' g₀ rel

  module _ {s : S} (f : ⟨ P s ⟩ → T) where
    {-
    include' :
      ((t : T) → (fiber f t → ⟨ H t ⟩) × (Σ[ g ∈ ⟨ G s ⟩ ] (is-stab' t f ∘ (σ s ⁺ G.inv g) ≡ is-stab' t f)))
        →
      (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩) ≃ (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩)
    include' k = {! !} where
      i→adj : (p : ⟨ P s ⟩)
        → (g : (Σ[ g ∈ ⟨ G s ⟩ ] (is-stab' (f p) f ∘ (σ s ⁺ G.inv g) ≡ is-stab' (f p) f)))
        → f p Eq.≡ f (G.inv (g .fst) σ.▷ p)
      i→adj p (g , stab) = Eq.sym $ transport (sym $ cong ⟨_⟩ $ stab ≡$ p) Eq.refl

      i→ : (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩) → (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩)
      i→ (p , q) =
        let
          (h-fib , g , stab) = k (f p)
          h = h-fib (p , refl)
        in (G.inv g σ.▷ p , Eq.transport (λ - → ⟨ Q - ⟩) (i→adj p (g , stab))  (h τ.▷ q))

      i← : (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩) → (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩)
      i← (p , q) =
        let
          (h-fib , g , stab) = k (f p)
          h = h-fib (p , refl)
          help : G.inv g σ.▷ (g σ.▷ p) ≡ p
          help = {! !}
          adj : f p Eq.≡ f (g σ.▷ p)
          adj = Eq.sym $ transport (cong ⟨_⟩ $ stab ≡$ (g σ.▷ p)) $ {! !}
        in (g σ.▷ p , Eq.transport (λ - → ⟨ Q - ⟩) adj (h τ.▷ q))

      i-iso : Iso _ _
      i-iso .Iso.fun = i→
      i-iso .Iso.inv = i←
      i-iso .Iso.rightInv (p , q) = ΣPathP ({! !} , {! !})
      i-iso .Iso.leftInv (p , q) using (_ , g , stab) ← k (f p) with i→adj p (g , stab)
      ... | Eq.refl = {! !}
    -}


    include :
      ((t : T) → (fiber f t → ⟨ H t ⟩) × (Σ[ g ∈ ⟨ G s ⟩ ] (is-stab t f ∘ (σ s ⁺ G.inv g) ≡ is-stab t f)))
        →
      (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩) ≃ (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩)
    include k = i→ , isoToIsEquiv i-iso where
      i→ : (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩) → (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩)
      i→ (p , q) =
        let
          (h-fib , g , stab) = k (f p)
          h = h-fib (p , refl)
          adj : f p ≡ f (G.inv g σ.▷ p)
          adj = sym $ transport (sym $ cong ⟨_⟩ $ stab ≡$ p) refl
        in (G.inv g σ.▷ p , subst (λ - → ⟨ Q - ⟩) adj (h τ.▷ q))

      i← : (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩) → (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩)
      i← (p , q) =
        let
          (h-fib , g , stab) = k (f p)
          h = h-fib (p , refl)
          help : G.inv g σ.▷ (g σ.▷ p) ≡ p
          help = {! !}
          adj : f p ≡ f (g σ.▷ p)
          adj = sym $ transport (cong ⟨_⟩ $ stab ≡$ (g σ.▷ p)) $ cong f help
        in (g σ.▷ p , subst (λ - → ⟨ Q - ⟩) adj (h τ.▷ q))

      i-iso : Iso _ _
      i-iso .Iso.fun = i→
      i-iso .Iso.inv = i←
      i-iso .Iso.rightInv (p , q) = ΣPathP ({! !} , {! !})
      i-iso .Iso.leftInv = {! !}

  include-mediate : (s : S) → (f f' : ⟨ P s ⟩ → T)
    → (g₀ : ⟨ G s ⟩)
    → (rel : f ≡ f' ∘ (σ s ⁺ g₀))
    → (k : ⟨ K*-Hasegawa s f ⟩)
    →
      equivFun (rwd g₀ rel) ∘ (equivFun (include f k)) ≡ equivFun (include f' (equivFun (mediate g₀ rel) k)) ∘ (equivFun (rwd g₀ rel))
  include-mediate s f f' g₀ rel k = funExt λ where
    (p , q) →
      let (h-fib , g , stab) = k (f p)
          (h-fib' , g' , stab') = k (f' (g₀ σ.▷ p))
          lem₁ =
            g₀ σ.▷ (G.inv g σ.▷ p) ≡⟨ {! !} ⟩
            G.inv (G.inv g₀ G.· g' G.· g₀) σ.▷ (g₀ σ.▷ p) ∎
      in
      ΣPathP (lem₁ , {! !})

  K*≤𝔖R : (s : S) (f : ⟨ P s ⟩ → T) → K*-Hasegawa s f ≤ 𝔖 ⟨ R* s f ⟩ˢ
  K*≤𝔖R s f = Inc where
    inc-hom : GroupHom (K*-Hasegawa s f) (𝔖 ⟨ R* s f ⟩ˢ)
    inc-hom .fst = include f
    inc-hom .snd = makeIsGroupHom {! !}

    Inc : _ ≤ _
    Inc .isSubgroup.inc = inc-hom
    Inc .isSubgroup.is-contr-ker-inc = {! !}

  -- K*≤𝔖R-wd : (s : S) (f f' : ⟨ P s ⟩ → T)
  --   → (g : ⟨ G s ⟩)
  --   → (p : PathP (λ i → ua (σ.action g) i → T) f f')
  --   → PathP (λ i → K*-Hasegawa s (p i) ≤ 𝔖 ⟨ R* s (p i) ⟩ˢ) (K*≤𝔖R s f) (K*≤𝔖R s f')
  -- K*≤𝔖R-wd = {! !}

  the-subgroup : (u : U) → Subgroup (𝔖 (Rˢ u)) (ℓ-suc ℓ)
  the-subgroup = uncurry λ s → SQ.elim (λ _ → isSetSubgroup) (sub s) {! !} where module _ (s : S) where
    -- sub' : (f : ⟨ P s ⟩ → T) → Subgroup (𝔖 ⟨ R* s f ⟩ˢ) (ℓ-suc ℓ)
    -- sub' f .fst = _
    -- sub' f .snd = K*≤𝔖R s f

    -- sub-eq : (f f' : ⟨ P s ⟩ → T) → (g₀ : ⟨ G s ⟩)
    --   -- → (p : f ≡ f' ∘ (σ _ ⁺ g₀))
    --   → (p : PathP (λ i → ua (σ.action g₀) i → T) f f')
    --   → PathP (λ i → ⟨ K*-Hasegawa s (p i)
    --   → {! isSubgroup.inc-fun (K*≤𝔖R s f)   !}
    -- sub-eq = ?

    sub : (f : ⟨ P s ⟩ → T) → Subgroup (𝔖 (Rˢ (s , [ f ]))) (ℓ-suc ℓ)
    sub f .fst = K*-Hasegawa s f
    sub f .snd = subst (K*-Hasegawa s f ≤_) {! !} (K*≤𝔖R s f)
    -}
    -}
