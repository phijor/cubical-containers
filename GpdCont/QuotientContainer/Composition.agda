module GpdCont.QuotientContainer.Composition where

open import GpdCont.Prelude
open import GpdCont.HomotopySet
import      GpdCont.Subuniverse
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Pi
open import GpdCont.GroupAction.Stabilizer using (module Setwise ; isPropIsStabilizer)
open import GpdCont.Group.SymmetricGroup using (𝔖)
open import GpdCont.Group.Subgroup
open import GpdCont.Group.DirProd
open import GpdCont.Group.Equivs using (conjEquiv)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset as ℙ using (ℙ)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Functions.Logic using (hProp≡)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Pi
open import Cubical.Algebra.Group.GroupPath using (isGroupoidGroup)
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_])
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)

{-
-- Setwise stabilizer
module Stabilizer {ℓ}
  (G : Group ℓ)
  (X : hSet ℓ)
  (σ : Action G X)
  where
  private module σ where
    open Action σ public
    open ActionProperties σ public

  open GroupStr (str G)

  StabPred : (S : ℙ ⟨ X ⟩) → ℙ ⟨ G ⟩
  StabPred S g .fst = (x : ⟨ X ⟩) → ⟨ S x ⟩ → ⟨ S (g σ.▷ x) ⟩
  StabPred S g .snd = isPropΠ2 λ x _ → str (S _)

  Stab⊂ : (S : ℙ ⟨ X ⟩) → Subgroup G
  Stab⊂ S .fst = StabPred S
  Stab⊂ S .snd .isSubgroup.id-closed x = subst (λ x → ⟨ S x ⟩) (sym (σ.action-1-id ≡$ x))
  Stab⊂ S .snd .isSubgroup.op-closed {x = g} {y = h} gˢ hˢ x = ghˢ where
    ghˢ' : ⟨ S x ⟩ → ⟨ S (h σ.▷ (g σ.▷ x)) ⟩
    ghˢ' s = hˢ (g σ.▷ x) $ gˢ x s

    ghˢ : ⟨ S x ⟩ → ⟨ S ((g · h) σ.▷ x) ⟩
    ghˢ s = subst (λ x → ⟨ S x ⟩) (sym (σ.action-comp g h ≡$ x)) (ghˢ' s)
  Stab⊂ S .snd .isSubgroup.inv-closed {x = g} gˢ x s = {!gˢ (inv g σ.▷ (g σ.▷ x)) !} where

    -gˢ : ⟨ S (inv g σ.▷ (g σ.▷ x)) ⟩ → ⟨ S (g σ.▷ (inv g σ.▷ (g σ.▷ x))) ⟩
    -gˢ = gˢ (inv g σ.▷ (g σ.▷ x))

    goal : ⟨ S (inv g σ.▷ x) ⟩
    goal = subst (λ y → ⟨ S (inv g σ.▷ y) ⟩) {!s!} {!gˢ !}

  Stab : (S : ℙ ⟨ X ⟩) → Group _
  Stab S = Subgroup→Group _ (Stab⊂ S)
-}


{-
module _ {ℓ}
  (S T : Type ℓ)
  (is-set-S : isSet S)
  (is-set-T : isSet T)
  (𝓤 : Type ℓ)
  (is-set-𝓤 : isSet 𝓤)
  (El : 𝓤 → hSet ℓ)
  (Σᵁ : (a : 𝓤) (b : ⟨ El a ⟩ → 𝓤) → 𝓤)
  (Pᵁ : S → 𝓤)
  (let P = El ∘ Pᵁ)
  (Qᵁ : T → 𝓤)
  (let Q = El ∘ Qᵁ)
  (G : S → Group ℓ)
  (σ : (s : S) → Action (G s) (P s))
  (H : T → Group ℓ)
  (τ : (t : T) → Action (H t) (Q t))
  where

  module σ {s} where
    open Action (σ s) public
    open ActionProperties (σ s) public
  module τ {t} = Action (τ t)
  module G {s} = GroupStr (str (G s))

  _∼_ : ∀ {s} → (f f' : ⟨ P s ⟩ → T) → Type _
  f ∼ f' = ∃[ g ∈ ⟨ G _ ⟩ ] f ≡ f' ∘ (g σ.▷_)

  ∼-symmetric : ∀ {s} {f f' : ⟨ P s ⟩ → T} → f ∼ f' → f' ∼ f
  ∼-symmetric = {! !}

  U : Type ℓ
  U = Σ[ s ∈ S ] ((⟨ P s ⟩ → T) / _∼_)

  -- TODO: Make sure that P and Q land in a proper universe of sets
  Rᵁ : U → 𝓤
  Rᵁ = uncurry λ s → SQ.rec is-set-𝓤 (λ f → Σᵁ (Pᵁ s) (Qᵁ ∘ f)) λ f f' → ∃-rec (is-set-𝓤 _ _) λ g f≡f'σg → {! !}

  R : U → hSet _
  R = El ∘ Rᵁ

  RΣ : (s : S) → (f : ⟨ P s ⟩ → T) → hSet _
  RΣ s f = ΣSet (P s) (Q ∘ f)

  RΣ≡R[-] : (s : S) → (f : ⟨ P s ⟩ → T) → RΣ s f ≡ R (s , [ f ])
  RΣ≡R[-] s f = {! !}

  Kᴰ⊂ : T → ((s , _) : U) → Subgroup (G s)
  Kᴰ⊂ t = uncurry λ s → SQ.rec (isSetSubgroup (G s)) (Kᴰ⊂* s) (well-defined s) where module _ (s : S) where
    open Stabilizer (G s) (P s) (σ s) using (Stab⊂ ; StabPred)
    module _ (f : ⟨ P s ⟩ → T) where
      is-stab : ℙ ⟨ P s ⟩
      is-stab p .fst = f p ≡ t
      is-stab p .snd = is-set-T (f p) t

      Kᴰ⊂* : Subgroup (G s)
      Kᴰ⊂* = Stab⊂ is-stab

    lemma : (f f' : ⟨ P s ⟩ → T) → f ∼ f' → StabPred (is-stab f) ℙ.⊆ StabPred (is-stab f')
    lemma f f' = ∃-rec (ℙ.⊆-isProp (StabPred (is-stab f)) (StabPred (is-stab f'))) λ g f≡f'σg (g' : ⟨ G s ⟩) s p f'p≡t →
      f' (g' σ.▷ p) ≡⟨ sym {! (f≡f'σg ≡$ p) !} ⟩
      f p ≡⟨ {! (f≡f'σg ≡$ p) !} ⟩
      t ∎

    lemma' : (f f' : ⟨ P s ⟩ → T) → f ∼ f' → StabPred (is-stab f') ℙ.⊆ StabPred (is-stab f)
    lemma' f f' = ∃-rec (ℙ.⊆-isProp (StabPred (is-stab f')) (StabPred (is-stab f))) goal
      where module _ (g : ⟨ G s ⟩) (r : f ≡ f' ∘ (g σ.▷_)) (g' : ⟨ G s ⟩) (fib : ∀ p → f' p ≡ t → f' (g' σ.▷ p) ≡ t) where
        goal : (p : ⟨ P s ⟩) → f p ≡ t → f (g' σ.▷ p) ≡ t
        goal p fp≡t = {! fib (G.inv g' σ.▷ p) !}
      -- λ g f≡f'σg (g' : ⟨ G s ⟩) s p fp≡t →
      -- -- f (g' σ.▷ p) ≡⟨ {! s!} ⟩
      -- -- t ∎
      -- -- {! sym (f≡f'σg ≡$ p) !}

    well-defined : (f f' : ⟨ P s ⟩ → T) → f ∼ f' → Kᴰ⊂* f ≡ Kᴰ⊂* f'
    well-defined f f' r = Σ≡Prop (isPropIsSubgroup (G s))
      $ curry (ℙ.⊆-extensionality (Kᴰ⊂* f .fst) (Kᴰ⊂* f' .fst))
        (lemma f f' r)
        (lemma f' f $ ∼-symmetric r)

  Kᴰ : T → U → Group ℓ
  Kᴰ t u = Subgroup→Group _ (Kᴰ⊂ t u)

  K : U → Group _
  K u = ΠGroup λ (t : T) → DirProd (H t) (Kᴰ t u)

  -- ΠActionΣ
  -- υ*'' : (s : S) (f : ⟨ P s ⟩ → T) → Action (K (s , [ f ])) (RΣ s f)
  -- υ*'' s f = {! ΠActionΣ (T , is-set-T)!}

  υ*' : (s : S) (f : ⟨ P s ⟩ → T) → Action (K (s , [ f ])) (RΣ s f)
  υ*' s f .Action.action k .fst = uncurry goal where
    module _ (p : ⟨ P s ⟩) (q : ⟨ Q (f p) ⟩ ) where
      h×kᴰ : ⟨ H (f p) ⟩ × ⟨ Kᴰ (f p) (s , [ f ]) ⟩
      h×kᴰ = k (f p)

      h : ⟨ H (f p) ⟩
      h = h×kᴰ .fst

      kᴰ : ⟨ Kᴰ (f p) (s , [ f ]) ⟩
      kᴰ = h×kᴰ .snd

      g : ⟨ G s ⟩
      g = kᴰ .fst

      p′ : ⟨ P s ⟩
      p′ = g σ.▷ p

      coh : f p ≡ f p′
      coh = sym $ kᴰ .snd p (refl′ (f p))

      q′ : ⟨ Q (f p′) ⟩
      q′ = subst (λ - → ⟨ Q - ⟩) coh (h τ.▷ q)

      goal : ⟨ RΣ s f ⟩
      goal .fst = p′
      goal .snd = q′

  υ*' s f .Action.action k .snd = {! !}
  υ*' s f .Action.pres· k k' = equivEq $ funExt $ uncurry λ p q → ΣPathP (goal₁ p q , {! !})
    where module _ (p : ⟨ P s ⟩) (q : ⟨ Q (f p) ⟩) where
      πᴳ : ⟨ K (s , [ f ]) ⟩ → ⟨ P s ⟩ → ⟨ G s ⟩
      πᴳ k p = k (f p) .snd .fst

      g = πᴳ k p
      g' = πᴳ k' p
      g'' = πᴳ k' (g σ.▷ p)

      goal₁ : (g G.· g') σ.▷ p ≡ g'' σ.▷ (g σ.▷ p)
      goal₁ =
        (g G.· g') σ.▷ p ≡⟨ σ.action-comp g g' ≡$ p ⟩
        g' σ.▷ (g σ.▷ p) ≡⟨ cong (λ t → (k' t) .snd .fst σ.▷ (g σ.▷ p)) $ sym (k (f p) .snd .snd p refl) ⟩
        g'' σ.▷ (g σ.▷ p) ∎

  υ*'-well-defined : (s : S) → (f f' : ⟨ P s ⟩ → T) → (r : f ∼ f') → PathP (λ i → Action (K (s , SQ.eq/ f f' r i)) {! (RΣ s (SQ.eq/ f f' r i))!}) {! !} {! !}
  υ*'-well-defined = {! !}

  υ* : (s : S) (f : ⟨ P s ⟩ → T) → Action (K (s , [ f ])) (R (s , [ f ]))
  υ* s f = subst (Action (K (s , [ f ]))) (RΣ≡R[-] s f) (υ*' s f)

  υ : (u : U) → Action (K u) (R u)
  υ = uncurry λ s → SQ.elim (λ _ → isSetAction) (υ* s) {! !}

  K⊂𝔖R : (u : U) → Subgroup (𝔖 (R u))
  K⊂𝔖R u .fst = {! !}
  K⊂𝔖R u .snd = {! !}
-}

module _ {ℓ}
  (𝓤 : hSet ℓ)
  (El : ⟨ 𝓤 ⟩ → hSet ℓ)
  (let open GpdCont.Subuniverse 𝓤 El)
  (strict-𝓤 : isStrict)
  (has-Σ : hasSigma)
  (S T : Type ℓ)
  (is-set-S : isSet S)
  (is-set-T : isSet T)
  (P : S → hSetSub)
  (Q : T → hSetSub)
  (G : S → Group ℓ)
  (σ : (s : S) → Action (G s) ⟨ P s ⟩ˢ)
  (H : T → Group ℓ)
  (τ : (t : T) → Action (H t) ⟨ Q t ⟩ˢ)
  where
  -- pt : ∥ 𝓤 ∥₂ → 𝓤
  -- pt = fst ∘ strict-𝓤
  open hasSigma has-Σ
  open Strict strict-𝓤

  module σ {s} where
    open Action (σ s) public
    open ActionProperties (σ s) public
  module τ {t} = Action (τ t)
  module G {s} = GroupStr (str (G s))
  module H {t} = GroupStr (str (H t))

  _∼_ : ∀ {s} → (f f' : ⟨ P s ⟩ → T) → Type _
  f ∼ f' = ∃[ g ∈ ⟨ G _ ⟩ ] f ≡ f' ∘ (g σ.▷_)

  ∼-symmetric : ∀ {s} {f f' : ⟨ P s ⟩ → T} → f ∼ f' → f' ∼ f
  ∼-symmetric {f} = ∃-map G.inv λ {g} f≡f'g →
    σ.precomp-inv g f≡f'g ∙ cong (f ∘_) (sym (σ.action-inv g))

  U : Type ℓ
  U = Σ[ s ∈ S ] ((⟨ P s ⟩ → T) / _∼_)

  -- On representatives of the quotient, we define the new positions using Σ-closure of 𝓤:
  R* : (s : S) (f : ⟨ P s ⟩ → T) → hSetSub
  R* s f = SubΣ (P s) (Q ∘ f)

  -- Since 𝓤-cardinals form a set, we can obtain the cardinality of the new positions for
  -- each shape `u : U`:  The cardinality does not depend on the chosen representative.
  ∣R∣ : U → Card
  ∣R∣ = uncurry λ s → SQ.rec isSetCard (∣_∣₂ ∘ R* s) (well-defined s) where
    module _ (s : S) where
      well-defined : (f f' : ⟨ P s ⟩ → T) → f ∼ f' → ∣ R* s f ∣₂ ≡ ∣ R* s f' ∣₂
      well-defined f f' = ∃-rec (ST.isSetSetTrunc _ _) λ g f≡f'σ →
        let e = Σ-cong-equiv (σ.action g) λ p → substEquiv (⟨_⟩ ∘ Q) (f≡f'σ ≡$ p)
        in cong ∣_∣₂ $ uaSub (R* s f) (R* s f') e

  -- 𝓤 is a strict subuniverse of sets, so we define the 𝓤-set of shapes `R u` as
  -- the canonical representative for the cardinality given above.
  R : U → hSetSub
  R = pt ∘ ∣R∣

  -- On any representative [ f ], the set of positions computes the representative in the
  -- component of `R* s f ≐ Σ (P s) (Q ∘ f)`:
  Rᵝ : (s : S) → (f : ⟨ P s ⟩ → T) → R (s , [ f ]) ≡ Representative (R* s f)
  Rᵝ s f = ptᵝ (R* s f)

  -- Cool fact 😎: The underlying types are definitionally the same
  ⟨Rᵝ⟩ : (s : S) → (f : ⟨ P s ⟩ → T) → ⟨ R (s , [ f ]) ⟩ ≡ ⟨ Representative (R* s f) ⟩
  ⟨Rᵝ⟩ s f = refl

  -- The 𝓤-sets of positions have an underlying sets:
  Rˢ : U → hSet _
  Rˢ = ⟨_⟩ˢ ∘ R

{------
  Lᴰ : ((s , _) : U) → Subgroup (ΠGroup λ (_ : T) → G s) ℓ
  Lᴰ = uncurry λ s → SQ.rec isSetSubgroup (Lᴰ* s) {! !} where module _ (s : S) where
    module _ (f : ⟨ P s ⟩ → T) where
      is-stab : (g : T → ⟨ G s ⟩) → Type _
      is-stab g = (p : ⟨ P s ⟩) → (t : T) → f (g t σ.▷ p) ≡ f p

      Lᴰ* : Subgroup (ΠGroup (const $ G s)) _
      Lᴰ* = isClosedSubset→Subgroup (ΠGroup (const $ G s))
        is-stab
        (λ g → isPropΠ2 λ p t → is-set-T _ (f p))
        (λ p t → cong f (σ.action-1-id ≡$ p))
        (λ {g} {h} pg ph p t → cong f (σ.action-comp (g t) (h t) ≡$ p) ∙ ph (g t σ.▷ p) t ∙ pg p t)
        (λ {g} pg p t → {! pg  !})
------}

  -- Given `s : S` and `f : P s → T`, the setwise stabilizer is a subgroup of `G s`.
  -- If `f ∼ f'`, then f and f' induce the same stabilizer subgroup. This defines a subgroup
  --
  --    Kᴰₜₛ ≤ Gₛ
  --
  -- for each `t : T` and `s : S`.
  is-stab : (t : T) → {s : S} (f : ⟨ P s ⟩ → T) → ℙ ⟨ P s ⟩
  is-stab t f p .fst = f p ≡ t
  is-stab t f p .snd = is-set-T (f p) t

  Kᴰ⊂ : T → ((s , _) : U) → Subgroup (G s) (ℓ-suc ℓ)
  Kᴰ⊂ t = uncurry λ s → SQ.rec isSetSubgroup (Kᴰ⊂* s) (well-defined s) where module _ (s : S) where
    module Stab where
      open Setwise (G s) ⟨ P s ⟩ˢ (σ s) public

    Kᴰ⊂* : (f : ⟨ P s ⟩ → T) → Subgroup _ _
    Kᴰ⊂* f = Stab.SetwiseStabilizerSubgroup (is-stab t f)

    module _ (f f' : ⟨ P s ⟩ → T) (g : ⟨ G s ⟩) (f≡f'g : f ≡ f' ∘ (g σ.▷_)) where
      is-stab-path : is-stab t f ≡ is-stab t f' ∘ (σ s ⁺ g)
      is-stab-path = ℙ.⊆-extensionality _ _ λ where
        .fst p fp≡t → sym (f≡f'g ≡$ p) ∙ fp≡t
        .snd p f'σp≡t → (f≡f'g ≡$ p) ∙ f'σp≡t

      -- XXX: This doesn't actually work.
      well-defined' : SubgroupPath (Kᴰ⊂* f) (Kᴰ⊂* f')
      well-defined' = Stab.equivSubset→SetwiseStabilizerSubgroupPath (is-stab t f) (is-stab t f') g is-stab-path

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
      is-stab-path : is-stab t f ≡ is-stab t f' ∘ (σ s ⁺ g)
      is-stab-path = ℙ.⊆-extensionality _ _ λ where
        .fst p fp≡t → sym (f≡f'g ≡$ p) ∙ fp≡t
        .snd p f'σp≡t → (f≡f'g ≡$ p) ∙ f'σp≡t

      stab-path : Kᴰ* f ≡ Kᴰ* f'
      stab-path = Stab.equivSubset→GroupPath (is-stab t f) (is-stab t f') g is-stab-path

    well-defined : (f f' : ⟨ P s ⟩ → T) → f ∼ f' → ∣Kᴰ∣* f ≡ ∣Kᴰ∣* f'
    well-defined f f' = ∃-rec (ST.isSetSetTrunc _ _) λ g p → cong ∣_∣₂ $ stab-path f f' g p

  ∣K∣ : U → ∥ Group (ℓ-suc ℓ) ∥₂
  ∣K∣ = uncurry λ s → SQ.rec ST.isSetSetTrunc (∣K∣* s) {! (well-defined s) !} where module _ (s : S) where
    module Stab where
      open Setwise (G s) ⟨ P s ⟩ˢ (σ s) public

    -- XXX: Should _⊗_ be a wreath product?
    K* : (f : ⟨ P s ⟩ → T) → Group _
    K* f = ΠGroup (λ (t : T) → H t ⊗ Stab.StabilizerGroup (is-stab t f))

    ∣K∣* : (f : ⟨ P s ⟩ → T) → ∥ Group _ ∥₂
    ∣K∣* f = ∣ K* f ∣₂

    {-
    module _ (f f' : ⟨ P s ⟩ → T) (g : ⟨ G s ⟩) (f≡f'g : f ≡ f' ∘ (g σ.▷_)) where
      is-stab-path : is-stab t f ≡ is-stab t f' ∘ (σ s ⁺ g)
      is-stab-path = ℙ.⊆-extensionality _ _ λ where
        .fst p fp≡t → sym (f≡f'g ≡$ p) ∙ fp≡t
        .snd p f'σp≡t → (f≡f'g ≡$ p) ∙ f'σp≡t

      stab-path : _ ≡ _
      stab-path = Stab.equivSubset→GroupPath (is-stab t f) (is-stab t f') g is-stab-path
    -}

    well-defined : (f f' : ⟨ P s ⟩ → T) → f ∼ f' → ∣K∣* f ≡ ∣K∣* f'
    well-defined f f' = ∃-rec (ST.isSetSetTrunc _ _) λ g p i → ∣ {! !} ∣₂


  υ : (u : U) → {! !}
  υ = {! !}

{-
  H×G : (s : S) (t : T) → Group ℓ
  H×G s t = DirProd (H t) (G s)

  H×Kᴰ⊂ : (t : T) (u : U) → Subgroup (H×G (u .fst) t) (ℓ-suc ℓ)
  H×Kᴰ⊂ t u = SubgroupDirProdRight (H t) {! (Kᴰ⊂ t u) !}

  ΠH×G : (s : S) → Group _
  ΠH×G s = (ΠGroup (H×G s))

  -- The families of subgroups Kᴰ naturally induce a subgroup on a large product:
  --
  --      Πₜ Hₜ × Kᴰₜₛ   ≤   Πₜ Hₜ × Gₛ
  K⊂ : (u : U) → Subgroup (ΠH×G (u .fst)) (ℓ-suc ℓ)
  K⊂ u = SubgroupΠ T _ λ t → H×Kᴰ⊂ t u

  K : (u : U) → Group _
  K u = K⊂ u .fst

  K⊂𝔖R : (u : U) → (K u) ≤ (𝔖 ⟨ R u ⟩ˢ)
  K⊂𝔖R = uncurry λ s → SQ.elim (λ _ → isSetIsSubgroup) [ s ]* {! !} where
    module _ (s : S) where
      module _ (f : ⟨ P s ⟩ → T) where
        ι→ :
          (∀ t → ⟨ H t ⟩ × (Σ[ g ∈ ⟨ G s ⟩ ] (is-stab t f ∘ (G.inv g σ.▷_)) ≡ is-stab t f))
            →
          (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩) → (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩)
        ι→ k (p , q) =
          let
            (h , g , stab-g) = k (f p)
            stab-g-p : (f (G.inv g σ.▷ p) ≡ f p) ≡ (f p ≡ f p)
            stab-g-p = cong fst $ stab-g ≡$ p
            stab-g-p' : (f (G.inv g σ.▷ p) ≡ f p)
            stab-g-p' = transport (sym stab-g-p) refl
          in (G.inv g σ.▷ p) , subst (⟨_⟩ ∘ Q) (sym stab-g-p') (h τ.▷ q)

        ι*  :
          (∀ t → ⟨ H t ⟩ × (Σ[ g ∈ ⟨ G s ⟩ ] (is-stab t f ∘ (G.inv g σ.▷_)) ≡ is-stab t f))
            →
          (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩) ≃ (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩)
        ι* k .fst = ι→ k
        ι* k .snd = {! !}

        ι : GroupHom (K (s , [ f ])) (𝔖 ⟨ R* s f ⟩ˢ)
        ι .fst = ι*
        ι .snd = makeIsGroupHom λ k k' → equivEq $ funExt λ where
          (p , q) → ΣPathP ({! !} , {! !})

        is-contr-ker-ι : isContrKer ι
        is-contr-ker-ι = isInjective→isContrKer ι inj where
          inj : (k : ⟨ K (s , [ f ]) ⟩) → ι* k ≡ idEquiv _ → k ≡ λ t → H.1g , G.1g , _
          inj k p = funExt λ t → ΣPathP (lemma₁ t , {! !}) where
            p' : ι→ k ≡ id (Σ _ _)
            p' = cong equivFun p

            p-ext : (pq : Σ _ _) → ι→ k pq ≡ pq
            p-ext = funExt⁻ p'

            lemma₁ : ∀ t → k t .fst ≡ H.1g
            lemma₁ t = {! k t .fst !}

            -- p-ext : ∀ {t} → ⟨ H t ⟩ → ⟨ G s ⟩ → ι→ 

        [-]' : isSubgroup (𝔖 ⟨ R* s f ⟩ˢ) (K (s , [ f ]))
        [-]' .isSubgroup.inc = ι
        [-]' .isSubgroup.is-contr-ker-inc = is-contr-ker-ι

        [_]* : isSubgroup (𝔖 ⟨ R (s , [ f ]) ⟩ˢ) (K (s , [ f ]))
        [_]* = {! ⟨ R (s , [ f ]) ⟩!}

-}

  {-
  -- Conjecture : Πₜ Hₜ × Gₛ is a subgroup of the new positions.
  ΠH×G≤𝔖R : (u : U) → isSubgroup (𝔖 ⟨ R u ⟩ˢ) (ΠH×G (u .fst))
  ΠH×G≤𝔖R = uncurry λ s → SQ.elim (λ _ → isSetIsSubgroup) ([-]* s) {! !} where
    [-]'' : (s : S) (f : ⟨ P s ⟩ → T) → isSubgroup (𝔖 ⟨ R* s f ⟩ˢ) (ΠH×G s)
    [-]'' s f .isSubgroup.inc .fst = {! !}
    [-]'' s f .isSubgroup.inc .snd = {! !}
    [-]'' s f .isSubgroup.is-contr-ker-inc = {! !}

    [-]' : (s : S) (f : ⟨ P s ⟩ → T) → isSubgroup (𝔖 ⟨ R (s , [ f ]) ⟩ˢ) (ΠH×G s)
    [-]' s f = {! ⟨ R (s , [ f ]) ⟩!}

    [-]* : (s : S) (f : ⟨ P s ⟩ → T) → isSubgroup (𝔖 ⟨ R (s , [ f ]) ⟩ˢ) (ΠH×G s)
    [-]* s f = {! ⟨ R (s , [ f ]) ⟩!}

  --      Πₜ Hₜ × Kᴰₜₛ   ≤   Πₜ Hₜ × Gₛ   ≤   𝔖( R s f )
  Full⊂ : (u : U) → Subgroup (𝔖 ⟨ R u ⟩ˢ) _
  Full⊂ u .fst = ΠH×G (u .fst)
  Full⊂ u .snd = ΠH×G≤𝔖R u
  -}

  -- Full⊂ : (u : U) → Subgroup (𝔖 ⟨ R u ⟩ˢ) _
  -- Full⊂ = uncurry λ s → SQ.elim (λ _ → isSetSubgroup) (Full⊂* s) {! !} where module _ (s : S) where
  --   Full⊂'' : (f : ⟨ P s ⟩ → T) → Subgroup (𝔖 ⟨ R* s f ⟩ˢ) (ℓ-suc ℓ)
  --   Full⊂'' f .fst = {!K⊂ !}
  --   Full⊂'' f .snd = {! !}

  --   Full⊂' : (f : ⟨ P s ⟩ → T) → Subgroup (𝔖 ⟨ Representative (R* s f) ⟩ˢ) (ℓ-suc ℓ)
  --   Full⊂' = {! !}

  --   -- TODO: These are subgroups of the same set of permutations, up to some proof of R being a set.
  --   Full⊂* : (f : ⟨ P s ⟩ → T) → Subgroup (𝔖 ⟨ R (s , [ f ]) ⟩ˢ) (ℓ-suc ℓ)
  --   Full⊂* f = {!  subst (λ - → Subgroup (𝔖 (⟨ Representative (R* s f) ⟩ , -)) (ℓ-suc ℓ)) {! !} (Full⊂' f) !}

{-
  K⊂Π[H×G] : (u : U) → Subgroup (ΠGroup λ (t : T) → DirProd (H t) (G (fst u)))
  K⊂Π[H×G] = {! !}

  K⊂𝔖R* : (s : S) → (f : ⟨ P s ⟩ → T) → Subgroup (𝔖 ⟨ R* s f ⟩ˢ)
  K⊂𝔖R* s f = {! !}

  -- TODO: To construct this from K⊂𝔖R*, we need to show that
  --
  --    𝔖 ⟨ R (s , [ f ]) ⟩ˢ
  --  ≡ 𝔖 ⟨ Representative (R* s f) ⟩ˢ
  --  ≡ 𝔖 ⟨ R* s f ⟩ˢ
  --
  -- The first step follows from the computation rule Rᵝ, but the second is
  -- more tricky: We know ∥ Representative X ≡ X ∥₁, but is that enough to show
  -- that X and `Representative X` have the same group of symmetries?  To prove
  -- this, we would have to exhibit a *canonical* isomorphism between these
  -- groups.
  K⊂𝔖R : (u : U) → Subgroup (𝔖 ⟨ R u ⟩ˢ)
  K⊂𝔖R = uncurry λ s → SQ.elim (λ _ → isSetSubgroup _)
    {! !}
    {! !}


{-
  υ*' : (s : S) (f : ⟨ P s ⟩ → T) → Action (K (s , [ f ])) (RΣ s f)
  υ*' s f .Action.action k .fst = uncurry goal where
    module _ (p : ⟨ P s ⟩) (q : ⟨ Q (f p) ⟩ ) where
      h×kᴰ : ⟨ H (f p) ⟩ × ⟨ Kᴰ (f p) (s , [ f ]) ⟩
      h×kᴰ = k (f p)

      h : ⟨ H (f p) ⟩
      h = h×kᴰ .fst

      kᴰ : ⟨ Kᴰ (f p) (s , [ f ]) ⟩
      kᴰ = h×kᴰ .snd

      g : ⟨ G s ⟩
      g = kᴰ .fst

      p′ : ⟨ P s ⟩
      p′ = g σ.▷ p

      coh : f p ≡ f p′
      coh = sym $ kᴰ .snd p (refl′ (f p))

      q′ : ⟨ Q (f p′) ⟩
      q′ = subst (λ - → ⟨ Q - ⟩) coh (h τ.▷ q)

      goal : ⟨ RΣ s f ⟩
      goal .fst = p′
      goal .snd = q′

  υ*' s f .Action.action k .snd = {! !}
  υ*' s f .Action.pres· k k' = equivEq $ funExt $ uncurry λ p q → ΣPathP (goal₁ p q , {! !})
    where module _ (p : ⟨ P s ⟩) (q : ⟨ Q (f p) ⟩) where
      πᴳ : ⟨ K (s , [ f ]) ⟩ → ⟨ P s ⟩ → ⟨ G s ⟩
      πᴳ k p = k (f p) .snd .fst

      g = πᴳ k p
      g' = πᴳ k' p
      g'' = πᴳ k' (g σ.▷ p)

      goal₁ : (g G.· g') σ.▷ p ≡ g'' σ.▷ (g σ.▷ p)
      goal₁ =
        (g G.· g') σ.▷ p ≡⟨ σ.action-comp g g' ≡$ p ⟩
        g' σ.▷ (g σ.▷ p) ≡⟨ cong (λ t → (k' t) .snd .fst σ.▷ (g σ.▷ p)) $ sym (k (f p) .snd .snd p refl) ⟩
        g'' σ.▷ (g σ.▷ p) ∎

  υ*'-well-defined : (s : S) → (f f' : ⟨ P s ⟩ → T) → (r : f ∼ f') → PathP (λ i → Action (K (s , SQ.eq/ f f' r i)) {! (RΣ s (SQ.eq/ f f' r i))!}) {! !} {! !}
  υ*'-well-defined = {! !}
-}

  υ* : (s : S) (f : ⟨ P s ⟩ → T) → Action (K (s , [ f ])) ⟨ R (s , [ f ]) ⟩ˢ
  υ* s f = subst (Action (K (s , [ f ]))) {! !} {! !} -- (RΣ≡R[-] s f) (υ*' s f)

  υ : (u : U) → Action (K u) ⟨ R u ⟩ˢ
  υ = uncurry λ s → SQ.elim (λ _ → isSetAction) (υ* s) {! !}
  -}
