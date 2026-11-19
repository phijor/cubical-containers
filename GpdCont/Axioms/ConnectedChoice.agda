module GpdCont.Axioms.ConnectedChoice where

open import GpdCont.Prelude
open import GpdCont.Connectivity as Connectivity
  using (merelyInh≃is1Connected ; isPropIsConnected ; isContr→isConnected ; isOfHLevel×isConnected→isContr)
open import GpdCont.Fibration
import      GpdCont.Suspension as Suspension
open import GpdCont.Axioms.TruncatedChoice
open import GpdCont.Axioms.LEM using (LEM ; DiscreteSetChoice ; discreteDiaconescu)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (hasSection ; hasRetract)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso ; invIso ; section ; retract ; isoToEquiv) renaming (_∎Iso to _Iso∎)
open import Cubical.Data.Sigma.Base
import Cubical.Data.Empty.Base as ⊥
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties as Nat using (+-comm)
open import Cubical.Data.Nat.Order as Nat≤ using (_≤_ ; _<_)
open import Cubical.Data.Sigma.Properties as Sigma
open import Cubical.HITs.Truncation as Tr using (∥_∥_)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.Susp as Susp using (Susp)
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv
open import Cubical.Homotopy.Connected

open import Cubical.Homotopy.Freudenthal using (isConnectedMerid)

private
  variable
    ℓ : Level
    X Y : Type ℓ

  pattern h-prop = 1
  pattern h-set = 2
  pattern h-groupoid = 3

-- The axiom of choice for sets can be generalized to higher h-levels in a different
-- direction to the one presented in the HoTT book by considering connectivity.

-- We say that a family of n-types (indexed by a set) has "k-connected choice" iff
-- it being pointwise k-connected implies it having a k-connected type of (global) sections.
--
-- In the following, we use this convention for h-levels:
-- · n - indexes n-types
-- · k - defines a level of (k)onnectivity

-- We turn this into an axiom:
-- The n-th axiom of k-connected choice says that all families of n-types satisfy k-connected choice.
hasConnectedChoice : (n k : HLevel) (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ n) → Type _
hasConnectedChoice n k X Y = ((x : ⟨ X ⟩) → isConnected k ⟨ Y x ⟩) → isConnected k ((x : ⟨ X ⟩) → ⟨ Y x ⟩)

-- As opposed to [hasChoice m n] above, having k-connected choice is a proposition:
isPropHasConnectedChoice : ∀ {n} (k : HLevel) (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ n) → isProp (hasConnectedChoice n k X Y)
isPropHasConnectedChoice _ _ _ = isPropΠ λ _ → isPropIsConnected

ACC : (ℓ : Level) (n k : HLevel) → Type _
ACC ℓ n k = ∀ (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ n) → hasConnectedChoice n k X Y

-- Again, this is a proposition, whereas AC(m, n) is not:
isPropACC : ∀ {ℓ} (n k : HLevel) → isProp (ACC ℓ n k)
isPropACC n k = isPropΠ2 λ X Y → isPropHasConnectedChoice k X Y

-- The axiom of (set) choice holds whenever a family of 1-connected sets has a
-- 1-connected type of (global) sections.
-- The reason for that is that being 1-connected means having contractible
-- propostional truncation — which is the case as soon as the truncation is inhabited.
hasSetChoice≃hasConnectedChoice[2,1] : (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) → hasSetChoice X Y ≃ hasConnectedChoice 2 1 X Y
hasSetChoice≃hasConnectedChoice[2,1] X Y = equiv→ (equivΠCod λ x → merelyInh≃is1Connected) merelyInh≃is1Connected

ASC≃ACC[2,1] : ASC ℓ ℓ ≃ ACC ℓ 2 1
ASC≃ACC[2,1] = equivΠCod λ X → equivΠCod λ Y → hasSetChoice≃hasConnectedChoice[2,1] X Y

-- For either n = 0 or k = 0, ACC(n, k) is a tautology:
--
-- ⋆ ACC(0, n): The conclusion is contractible, thus k-connected for any k.
ACC[0,_] : (k : HLevel) → ACC ℓ 0 k
ACC[0, k ] X Y = hasConnectedChoice₀ where
  hasConnectedChoice₀ : ((x : ⟨ X ⟩) → isConnected k ⟨ Y x ⟩) → isConnected k ((x : ⟨ X ⟩) → ⟨ Y x ⟩)
  hasConnectedChoice₀ unused-assumption = isContr→isConnected k (isContrΠ (str ∘ Y))

-- ⋆ ACC(n, 0): The conclusion is always 0-connected.
ACC[_,0] : (n : HLevel) → ACC ℓ n 0
ACC[ n ,0] X Y _ = isConnectedZero (∀ x → ⟨ Y x ⟩)

-- ⋆ The above-diagonal ACC(n, k + n) is a tautology.
--
-- This follows from the fact that any k-connected family
-- of k-types is pointwise contractible.
ACC[_,_+] : (n k : HLevel) → ACC ℓ n (k + n)
ACC[_,_+] n k X Y conn-Y = isContr→isConnected (k + n) isContr-Sections where
  isContrY : ∀ x → isContr ⟨ Y x ⟩
  isContrY x = isOfHLevel×isConnected→isContr n ⟨ Y x ⟩
    (str (Y x))
    (isConnectedSubtr n k (conn-Y x))

  isContr-Sections : isContr (Section (⟨_⟩ ∘ Y))
  isContr-Sections = isOfHLevelSection 0 isContrY

-- ⋆ ACC(1, 1+k): A special case of the above.
ACC[1,1+_] : (k : HLevel) → ACC ℓ 1 (suc k)
ACC[1,1+ k ] = subst (ACC _ 1) (+-comm k 1) ACC[ 1 , k +]

-- ACC[+1,+1]→ACC : (n k : HLevel) → ACC ℓ (suc n) (suc k) → ACC ℓ n k
-- ACC[+1,+1]→ACC n k acc-suc X Y conn-Y = {!acc-suc _ _ _ !}

-- ACC→ACC[+1,+1] : (n k : HLevel) → ACC ℓ n k → ACC ℓ (suc n) (suc k)
-- ACC→ACC[+1,+1] n k acc X Y conn-Y = {!acc _ _ _ !}

-- Being "split" can similarly be generalized to higher h-levels:
-- A function is k-split if it has an k-connected type of sections.
isConnectedHasSection : (k : HLevel) (f : X → Y) → Type _
isConnectedHasSection k f = isConnected k (hasSection f)

-- foo : (k : HLevel) (f : X → Y) → isConnectedHasSection k f ≃ isConnected k (Σ[ g ∈ (Y → X) ] (∀ y → f (g y) ≡ y))
-- foo k f = {! !}

-- This too is a proposition, again because "being connected" is a proposition:
isPropHasConnectedSections : (k : HLevel) (f : X → Y) → isProp (isConnectedHasSection k f)
isPropHasConnectedSections k f = isPropIsConnected

-- For n=1 the two notions coincide:
--
-- Being split (= merely having a section) is the same as having a 1-connected type of sections.
isSplit≃has1ConnectedSections : {f : X → Y} → isSplit f ≃ isConnectedHasSection 1 f
isSplit≃has1ConnectedSections = merelyInh≃is1Connected

-- We turn "every surjection between sets has a section" into its analogue for higher
-- h-levels and notions of connectivity:
--
-- CFCS(n,k): Every k-connected map from an n-type onto a set has a k-connected space of sections.
ConnectedFunsHaveConnectedSections : (ℓ : Level) (n k : HLevel) → Type _
ConnectedFunsHaveConnectedSections ℓ n k =
  ∀ (X : TypeOfHLevel ℓ n)
    (Y : hSet ℓ)
    (f : ⟨ X ⟩ → ⟨ Y ⟩)
  → isConnectedFun k f
  ---------------------------
  → isConnectedHasSection k f

isPropConnectedFunsHaveConnectedSections : ∀ {ℓ} (n k : HLevel) → isProp (ConnectedFunsHaveConnectedSections ℓ n k)
isPropConnectedFunsHaveConnectedSections n k = isPropΠ4 λ X Y f conn → isPropHasConnectedSections k f

isSurjection≃is1ConnectedFun : ∀ {X Y : Type ℓ} (f : X → Y) → isSurjection f ≃ isConnectedFun 1 f
isSurjection≃is1ConnectedFun f = equivΠCod λ b → merelyInh≃is1Connected

-- Consistency check: All surjections split iff 1-connected maps between sets have 1-connected sections.
AllSurjectionsSplit≃ConnectedFunsHaveConnectedSections₂₁ : AllSurjectionsSplit ℓ ≃ ConnectedFunsHaveConnectedSections ℓ 2 1
AllSurjectionsSplit≃ConnectedFunsHaveConnectedSections₂₁ =
  equivΠCod λ X → equivΠCod λ Y → equivΠCod λ f → equiv→ (isSurjection≃is1ConnectedFun f) (isSplit≃has1ConnectedSections {f = f})

-- For low n and k, CFCS is a tautology:
-- Any type is 0-connected, so CFCS(n, 0) holds for all n.
ConnectedFunsHaveConnectedSections[_,0] : (n : HLevel) → ConnectedFunsHaveConnectedSections ℓ n 0
ConnectedFunsHaveConnectedSections[ n ,0] X Y f _ = isConnectedZero (hasSection f)

-- For contractible domains, 1-connected functions are very strong: They have a unique section.
--
-- The idea is the following:  A function from a contractible type is just a point
-- in the codomain.  1-connectivity of the function ensures that all of its fibers
-- are merely inhabited, which is enough to show that the constant map back is a
-- section.  But the type of sections of f happens to be a proposition, thus contractible.
isContrDomain→1ConnectedFunHaveContrSections :
  ∀ (X : TypeOfHLevel ℓ 0) (Y : hSet ℓ)
  → (f : ⟨ X ⟩ → ⟨ Y ⟩)
  → (isConnectedFun 1 f)
  → isContr (hasSection f)
isContrDomain→1ConnectedFunHaveContrSections (X , is-contr-X) (Y , is-set-Y) f 1-conn-f = isContrHasSection-f where
  x₀ : X
  x₀ = is-contr-X .fst

  one-inh-fiber : ∀ y → fiber f y → f x₀ ≡ y
  one-inh-fiber y (x , p) = cong f (is-contr-X .snd x) ∙ p

  inh-fib : ∀ y → ∥ fiber f y ∥ 1
  inh-fib y = 1-conn-f y .fst

  sec-f-const : section f (const x₀)
  sec-f-const y = Tr.rec₊ {B = f x₀ ≡ y} (is-set-Y (f x₀) y) (one-inh-fiber y) (inh-fib y)

  section-f-equiv : hasSection f ≃ (∀ y → f x₀ ≡ y)
  section-f-equiv =
    hasSection f ≃⟨⟩
    Σ[ g ∈ (Y → X) ] section f g ≃⟨ Σ-contractFst (isContrΠ λ _ → is-contr-X) ⟩
    section f (const x₀) ≃⟨⟩
    (∀ y → f x₀ ≡ y) ≃∎

  isPropHasSection-f : isProp (hasSection f)
  isPropHasSection-f = isOfHLevelRespectEquiv 1 (invEquiv section-f-equiv) (isPropΠ λ y → is-set-Y (f x₀) y)

  isContrHasSection-f : isContr (hasSection f)
  isContrHasSection-f = inhProp→isContr (const x₀ , sec-f-const) isPropHasSection-f

-- The above contractibility lemma allows us to prove
--  ⋆ CFCS(0, 1 + k): 1-connected functions from contractible types have 1-connected sections.
ConnectedFunsHaveConnectedSections[0,1+_] : ∀ k → ConnectedFunsHaveConnectedSections ℓ 0 (suc k)
ConnectedFunsHaveConnectedSections[0,1+ k ] X Y f 1+k-conn-f =
  isContr→isConnected (suc k)
  (isContrDomain→1ConnectedFunHaveContrSections X Y f 1-conn-f) where
  1-conn-f : isConnectedFun 1 f
  1-conn-f = isConnectedFun≤ 1 (suc k) f (Nat≤.suc-≤-suc Nat≤.zero-≤) 1+k-conn-f

-- CFCSSuc→CFCS : (n k : HLevel) → ConnectedFunsHaveConnectedSections ℓ (suc n) (suc k) → ConnectedFunsHaveConnectedSections ℓ n k
-- CFCSSuc→CFCS n k cfcs-suc X Y f k-conn-f = {! !}


--  ⋆ ACC implies that connected functions have connected sections.
--
-- Proof.  We prove the implication ACC(n, k) ⇒ CFCS(n, k) for n > 0.
-- For n = 0, the conclusion is a tautology.
--
-- Consider the family of fibers of a function f : X → Y:
-- Assuming connected choice for this family, we can turn the statement
--  "f is k-connected" (≃ "f has k-connected fibers")
-- into
--  "global sections of the fibers of f are k-connected".
-- But these global sections are exactly the (usual) sections of f,
-- therefore k-connected, too.
module FiberConnectivity {n : HLevel} (X : TypeOfHLevel ℓ (suc n)) (Y : hSet ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) where
  private
    n⁺ = suc n

  fiberOfHLevel : (y : ⟨ Y ⟩) → TypeOfHLevel ℓ n⁺
  fiberOfHLevel y .fst = fiber f y
  fiberOfHLevel y .snd = isOfHLevelΣ n⁺ (str X) λ x → isProp→isOfHLevelSuc n (str Y (f x) y)

  hasConnectedChoiceFiber→isConnectedHasSection : (k : HLevel) → hasConnectedChoice n⁺ k Y fiberOfHLevel → (isConnectedFun k f → isConnectedHasSection k f)
  hasConnectedChoiceFiber→isConnectedHasSection k conn-choice conn-f = goal where
    -- Connected choice says that global sections of `fiber f` are k-connected:
    hasConnectedFiberSections : isConnected k (Section $ fiber f)
    hasConnectedFiberSections = conn-choice conn-f

    goal : isConnectedHasSection k f
    goal = isConnectedRetractFromIso k
      (hasSection-fiberSection-Iso f)
      hasConnectedFiberSections

ACC→ConnectedFunsHaveConnectedSections-[1+_,_] : (n k : HLevel) → ACC ℓ (suc n) k → ConnectedFunsHaveConnectedSections ℓ (suc n) k
ACC→ConnectedFunsHaveConnectedSections-[1+_,_] n k conn-choice X Y f conn-f = F.hasConnectedChoiceFiber→isConnectedHasSection k (conn-choice Y F.fiberOfHLevel) conn-f where
  module F = FiberConnectivity X Y f

-- ⋆ ACC(n, k) ⇒ CFCS(n, k).
ACC→ConnectedFunsHaveConnectedSections : (n k : HLevel) → ACC ℓ n k → ConnectedFunsHaveConnectedSections ℓ n k
ACC→ConnectedFunsHaveConnectedSections zero zero _ = ConnectedFunsHaveConnectedSections[ 0 ,0]
ACC→ConnectedFunsHaveConnectedSections zero (suc k) _ = ConnectedFunsHaveConnectedSections[0,1+ k ]
ACC→ConnectedFunsHaveConnectedSections (suc n) k = ACC→ConnectedFunsHaveConnectedSections-[1+ n , k ]

-- If connected functions have connected sections, then ACC holds.
--
-- Proof.  We prove CFCS(n, k) ⇒ ACC(n, k) for n ≥ 2. In the remaining
-- cases the conclusion is a tautology.  Consider the total fibration
-- `proj : Σ X Y → X`.  If Y is pointwise k-connected, then proj is a
-- k-connected function.  Using our assumption, we can conclude that
-- proj has k-connected sections.  But the sections of proj are exactly
-- the global sections of Y, thus those are k-connected.
module TotalFibrationConnectivity {n : HLevel} (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ (2 + n)) where
  module T = Total ⟨ X ⟩ (⟨_⟩ ∘ Y)

  open T using (proj) public
  open T using (Total ; isOfHLevelTotal ; proj)

  TotalOfHLevel : TypeOfHLevel ℓ (2 + n)
  TotalOfHLevel .fst = Total
  TotalOfHLevel .snd = isOfHLevelTotal (2 + n) (isOfHLevelPlus' 2 (str X)) (str ∘ Y)

  isConnectedFam→isConnectedFunProj : ∀ k → (∀ x → isConnected k ⟨ Y x ⟩) → isConnectedFun k proj
  isConnectedFam→isConnectedFunProj k conn-fam x = conn-fibers where
    conn-fibers : isConnected k (fiber proj x)
    conn-fibers = isConnectedRetractFromIso k (T.fiberProj-Family-Iso x) (conn-fam x)

  isConnectedHasSection→hasConnectedChoiceFiber : (k : HLevel) → (isConnectedFun k proj → isConnectedHasSection k proj) → hasConnectedChoice (2 + n) k X Y
  isConnectedHasSection→hasConnectedChoiceFiber k conn-proj→conn-sec-proj conn-fam = isConnectedFam where
    isConnectedFunProj : isConnectedFun k proj
    isConnectedFunProj = isConnectedFam→isConnectedFunProj k conn-fam

    hasConnectedSectionsProj : isConnectedHasSection k proj
    hasConnectedSectionsProj = conn-proj→conn-sec-proj isConnectedFunProj

    global-section-Section-proj-Iso : Iso (Section $ λ x → ⟨ Y x ⟩) (hasSection proj)
    global-section-Section-proj-Iso = invIso T.hasSectionProj-SectionFam-Iso

    isConnectedFam : isConnected k (∀ x → ⟨ Y x ⟩)
    isConnectedFam = isConnectedRetractFromIso k global-section-Section-proj-Iso hasConnectedSectionsProj

ConnectedFunsHaveConnectedSections→ACC-[2+_,_] : (n k : HLevel) → ConnectedFunsHaveConnectedSections ℓ (2 + n) k → ACC ℓ (2 + n) k
ConnectedFunsHaveConnectedSections→ACC-[2+_,_] n k conn-fun→conn-sec X Y = F.isConnectedHasSection→hasConnectedChoiceFiber k (conn-fun→conn-sec F.TotalOfHLevel X F.proj) where
  module F = TotalFibrationConnectivity X Y

ConnectedFunsHaveConnectedSections→ACC-[0,_] : (k : HLevel) → ConnectedFunsHaveConnectedSections ℓ 0 k → ACC ℓ 0 k
ConnectedFunsHaveConnectedSections→ACC-[0,_] k _ = ACC[0, k ]

ConnectedFunsHaveConnectedSections→ACC-[1,0] : ConnectedFunsHaveConnectedSections ℓ 1 0 → ACC ℓ 1 0
ConnectedFunsHaveConnectedSections→ACC-[1,0] _ = ACC[ 1 ,0]

ConnectedFunsHaveConnectedSections→ACC : (n k : HLevel) → ConnectedFunsHaveConnectedSections ℓ n k → ACC ℓ n k
ConnectedFunsHaveConnectedSections→ACC 0 k = const ACC[0, k ]
ConnectedFunsHaveConnectedSections→ACC 1 0 = const ACC[ 1 ,0]
ConnectedFunsHaveConnectedSections→ACC 1 (suc k) = const ACC[1,1+ k ]
ConnectedFunsHaveConnectedSections→ACC (suc (suc n)) k = ConnectedFunsHaveConnectedSections→ACC-[2+ n , k ]

-- Theorem: ACC(n,k) is equivalent to all k-connected functions having k-connected sections.
ACC≃ConnectedFunsHaveConnectedSections : (n k : HLevel) → ACC ℓ n k ≃ ConnectedFunsHaveConnectedSections ℓ n k
ACC≃ConnectedFunsHaveConnectedSections n k = propBiimpl→Equiv
  (isPropACC n k)
  (isPropConnectedFunsHaveConnectedSections n k)
  (ACC→ConnectedFunsHaveConnectedSections n k)
  (ConnectedFunsHaveConnectedSections→ACC n k)


-- ACC is additive in k, for k ≥ 1.
-- For k = 0, the below is equivalent to ACC(n, 1).
ACC[n,1+]→ACC[n,2+] : (n k : HLevel) → 1 ≤ k → ACC ℓ n k → ACC ℓ n (suc k)
ACC[n,1+]→ACC[n,2+] n zero 1≤0 acc X Y is-conn-suc-Y = ⊥.rec (Nat≤.¬-<-zero 1≤0)
ACC[n,1+]→ACC[n,2+] n k@(suc k-1) _ acc X Y is-conn-suc-Y = is-suc-connected-section where
  is-conn-Y : ∀ x → isConnected k ⟨ Y x ⟩
  is-conn-Y = isConnectedSubtr k 1 ∘ is-conn-suc-Y

  ΠY : Type _
  ΠY = ∀ x → ⟨ Y x ⟩

  is-conn-ΠY : isConnected k ΠY
  is-conn-ΠY = acc X Y is-conn-Y

  -- 1) Sections of Y are merely inhabited.
  inh-ΠY : ∥ ΠY ∥₁
  inh-ΠY = Connectivity.isConnectedSuc→merelyInh k-1 is-conn-ΠY

  _≡Π_ : (f g : ΠY) → Type _
  _≡Π_ f g = ∀ x → f x ≡ g x

  SIP-Π : ∀ {f g} → (f ≡ g) ≃ (f ≡Π g)
  SIP-Π = invEquiv funExtEquiv

  isOfHLevel-≡Π : (f g : ΠY) → ∀ x → isOfHLevel n (f x ≡ g x)
  isOfHLevel-≡Π f g x = isOfHLevelPath n (str (Y x)) (f x) (g x)

  is-connected-≡Π : ∀ f g → isConnected k (f ≡Π g)
  is-connected-≡Π f g = acc X
    (λ x → (f x ≡ g x) , isOfHLevel-≡Π f g x)
    (λ x → isConnectedPath k (is-conn-suc-Y x) (f x) (g x))

  -- 2) Sections of Y have k-connected path spaces.
  is-connected-path : ∀ (f g : ∀ x → ⟨ Y x ⟩) → isConnected k (f ≡ g)
  is-connected-path f g = isConnectedRetractFromIso k (equivToIso SIP-Π) (is-connected-≡Π f g)

  is-suc-connected-section : isConnected (suc k) (∀ x → ⟨ Y x ⟩)
  is-suc-connected-section = Connectivity.merelyInh×isConnectedPath→isConnectedSuc k
    inh-ΠY
    is-connected-path

ACC[n,1]×ACC[n,-]→ACC[n,suc-] : (n k : HLevel) → ACC ℓ n 1 → ACC ℓ n k → ACC ℓ n (suc k)
ACC[n,1]×ACC[n,-]→ACC[n,suc-] n k acc-set acc X Y conn-Y = is-suc-connected-section where
  ΠY = ∀ x → ⟨ Y x ⟩

  inh×conn-Y : ∀ x → ∥ ⟨ Y x ⟩ ∥₁ × ∀ (y y′ : ⟨ Y x ⟩) → isConnected k (y ≡ y′)
  inh×conn-Y x = (invEq $ Connectivity.merelyInh×isConnectedPath≃isConnectedSuc k) $ (conn-Y x)

  is-1-conn-Y : ∀ x → isConnected 1 ⟨ Y x ⟩
  is-1-conn-Y x = equivFun merelyInh≃is1Connected (inh×conn-Y x .fst)

  is-k-conn-Path-Y : ∀ x (y y′ : ⟨ Y x ⟩) → isConnected k (y ≡ y′)
  is-k-conn-Path-Y x = inh×conn-Y x .snd

  inh-section : ∥ (∀ x → ⟨ Y x ⟩) ∥₁
  inh-section = invEq Connectivity.merelyInh≃is1Connected $ acc-set X Y is-1-conn-Y

  Π-Path : (f g : ∀ x → ⟨ Y x ⟩) → Type _
  Π-Path f g = ∀ x → f x ≡ g x

  Path-Π-Path-equiv : ∀ {f g} → (f ≡ g) ≃ (Π-Path f g)
  Path-Π-Path-equiv = invEquiv funExtEquiv

  isOfHLevel-Π-Path : (f g : ∀ x → ⟨ Y x ⟩) → ∀ x → isOfHLevel n (f x ≡ g x)
  isOfHLevel-Π-Path f g x = isOfHLevelPath n (str (Y x)) (f x) (g x)

  Π-Path-n-Type : (f g : ΠY) (x : ⟨ X ⟩) → TypeOfHLevel _ n
  Π-Path-n-Type f g x .fst = f x ≡ g x
  Π-Path-n-Type f g x .snd = isOfHLevel-Π-Path f g x

  is-connected-Π-Path-ext : ∀ (f g : ΠY) x → isConnected k (f x ≡ g x)
  is-connected-Π-Path-ext f g x = is-k-conn-Path-Y x (f x) (g x)

  is-connected-Π-Path : ∀ f g → isConnected k (Π-Path f g)
  is-connected-Π-Path f g = acc X (Π-Path-n-Type f g) $ is-connected-Π-Path-ext f g

  is-connected-path : ∀ (f g : ∀ x → ⟨ Y x ⟩) → isConnected k (f ≡ g)
  is-connected-path f g = isConnectedRetractFromIso k (equivToIso Path-Π-Path-equiv) (is-connected-Π-Path f g)

  is-suc-connected-section : isConnected (suc k) (∀ x → ⟨ Y x ⟩)
  is-suc-connected-section = Connectivity.merelyInh×isConnectedPath→isConnectedSuc k
    inh-section
    is-connected-path

ACC-subtr : ∀ d {n k} → ACC ℓ (d + n) k → ACC ℓ n k
ACC-subtr d acc X Y = acc X λ x → ⟨ Y x ⟩ , isOfHLevelPlus d (str (Y x))

Δ : (ℓ : Level) (j : HLevel) → Type _
Δ ℓ j = ACC ℓ (suc j) j

isPropΔ : ∀ j → isProp (Δ ℓ j)
isPropΔ j = isPropACC (suc j) j

--- Δ(1) is the ordinary axiom of choice.
_ : ∀ ℓ → Δ ℓ 1 ≃ AllSurjectionsSplit ℓ
_ = λ ℓ → ACC≃ConnectedFunsHaveConnectedSections 2 1 ∙ₑ invEquiv AllSurjectionsSplit≃ConnectedFunsHaveConnectedSections₂₁

ACC→Δ : ∀ {n k} → k < n → ACC ℓ n k → Δ ℓ k
ACC→Δ {n} {k} k<n@(d , d+1+k≡n) acc = ACC-subtr d $ subst (λ n → ACC _ n k) (sym d+1+k≡n) acc

private
  ACC[suc]×Δ→ACC' : ∀ d k → ACC ℓ (d + suc k) (suc k) → Δ ℓ k → ACC ℓ (d + suc k) k
  ACC[suc]×Δ→ACC' d k acc δ X Y is-conn-Y =
    -- Our goal is to show that sections of Y are k-connected.
    the (isConnected k ΠY) goal where

    -- Sections of Y.
    ΠY : Type _
    ΠY = ∀ x → ⟨ Y x ⟩

    -- The family of k+1-truncations of Y.
    ∥Y∥ : ⟨ X ⟩ → TypeOfHLevel _ (suc k)
    ∥Y∥ x .fst = ∥ ⟨ Y x ⟩ ∥ (suc k)
    ∥Y∥ x .snd = Tr.isOfHLevelTrunc (suc k)

    -- Sections of this family.
    Π∥Y∥ : Type _
    Π∥Y∥ = ∀ x → ∥ ⟨ Y x ⟩ ∥ (suc k)

    -- Note that precomposition with the truncation map induces a map
    -- from sections of Y to sections of ∥Y∥:
    tr : ∀ x → ⟨ Y x ⟩ → ⟨ ∥Y∥ x ⟩
    tr x = Tr.∣_∣ₕ

    tr* : ΠY → Π∥Y∥
    tr* = Tr.∣_∣ₕ ∘_

    -- In order to show that sections of Y are k-connected, it suffices to show that:
    -- 1) Π(∥Y∥) is k-connected.
    -- 2) the map tr* : Π(Y) → Π(∥Y∥) is k-connected.
    goal : isConnected k ΠY
    goal = Connectivity.isConnectedFun→isConnectedDomain k tr*
      is-conn-tr*
      is-conn-Π∥Y∥
      where
      -- (Y x) is k-connected, so its truncations above k are k-connected as well.
      is-conn-∥Y∥ : ∀ x → isConnected k (∥ ⟨ Y x ⟩ ∥ (suc k))
      is-conn-∥Y∥ x = Connectivity.isConnected→isConnectedTruncPlus 1 k (is-conn-Y x)

      -- 1) It follows from Δ(k) that sections of ∥Y∥ are k-connected.
      is-conn-Π∥Y∥ : isConnected k Π∥Y∥
      is-conn-Π∥Y∥ = δ X ∥Y∥ is-conn-∥Y∥

      -- We need to show that all fibers of tr* are k-connected.
      is-conn-tr* : isConnectedFun k tr*
      is-conn-tr* t = is-conn-tr*-fiber where
        -- To do so, we observe that tr*-fibers are equivalent
        -- to an X-indexed family of (d+1+k)-types, namely fibers of tr:
        Fib : ⟨ X ⟩ → TypeOfHLevel _ (d + suc k)
        Fib x .fst = fiber (tr x) (t x)
        Fib x .snd = isOfHLevelΣ (d + suc k) (str (Y x)) λ y → isOfHLevelPlus d Tr.isOfHLevelTruncPath

        tr*-fiber-equiv : (∀ x → ⟨ Fib x ⟩) ≃ fiber tr* t
        tr*-fiber-equiv =
          (∀ x → Σ[ y ∈ ⟨ Y x ⟩ ] Tr.∣ y ∣ₕ ≡ t x)
            ≃⟨ Σ-Π-≃ ⟩
          Σ[ s ∈ (∀ x → ⟨ Y x ⟩) ] (∀ x → Tr.∣ s x ∣ₕ ≡ t x)
            ≃⟨ Σ-cong-equiv-snd (λ s → funExtEquiv) ⟩
          Σ[ s ∈ (∀ x → ⟨ Y x ⟩) ] Tr.∣_∣ₕ ∘ s ≡ t
            ≃∎

        -- tr(x) : Y(x) → ∥Y(x)∥ₖ₊₁ is always (k+1)-connected.
        is-conn-suc-tr : ∀ x → isConnectedFun (suc k) (tr x)
        is-conn-suc-tr x = Connectivity.isConnectedFunTrunc (suc k)

        -- Consequently, Fib(x) is (k+1)-connected (it is one particular fiber of tr).
        is-conn-suc-Fib : ∀ x → isConnected (suc k) ⟨ Fib x ⟩
        is-conn-suc-Fib x = is-conn-suc-tr x (t x)

        -- But this means that Fib satisfies the hypotheses of ACC(d+1+k, k+1):
        -- 1. It is a family of (d+1+k)-types, that are
        -- 2. pointwise (k+1)-connected.
        -- Hence, Π(Fib) is (k+1)-connected.
        is-conn-suc-ΠFib : isConnected (suc k) (∀ x → ⟨ Fib x ⟩)
        is-conn-suc-ΠFib = acc X Fib is-conn-suc-Fib

        -- Transporting back along the equivalence, this means that all fibers of tr* are (k+1)-connected.
        is-conn-suc-tr*-fiber : isConnected (suc k) (fiber tr* t)
        is-conn-suc-tr*-fiber = Connectivity.isConnectedRespectEquiv (suc k) tr*-fiber-equiv is-conn-suc-ΠFib

        -- (k+1)-connected types are also k-connected, hence tr* has k-connected fibers.
        is-conn-tr*-fiber : isConnected k (fiber tr* t)
        is-conn-tr*-fiber = isConnectedSubtr k 1 is-conn-suc-tr*-fiber

ACC[suc]×Δ→ACC : ∀ n k → k < n → ACC ℓ n (suc k) → Δ ℓ k → ACC ℓ n k
ACC[suc]×Δ→ACC n k k<n@(d , d+1+k≡n) = subst (λ n → ACC _ n (suc k) → Δ _ k → ACC _ n k) d+1+k≡n
  $ ACC[suc]×Δ→ACC' d k

ACC≃ACC[suc]×Δ : ∀ n k → 1 ≤ k → k < n → ACC ℓ n k ≃ (ACC ℓ n (suc k) × Δ ℓ k)
ACC≃ACC[suc]×Δ n k 1≤k k<n = propBiimpl→Equiv
  (isPropACC n k)
  (isProp× (isPropACC n (suc k)) (isPropΔ k))
  (λ acc → (ACC[n,1+]→ACC[n,2+] n k 1≤k acc) , (ACC→Δ k<n acc))
  (uncurry $ ACC[suc]×Δ→ACC n k k<n)

-- ACC≃ΠΔ : ∀ n k → 1 ≤ k → k < n → ACC ℓ n k ≃ (∀ j → k ≤ j → j < n → Δ ℓ j)
-- ACC≃ΠΔ n k 1≤k k<n = {! !}

module Desuspension {ℓ}
  (j : HLevel) (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ (1 + j))
  where
  open Susp.Susp using (north ; south ; merid)

  private
    ΣY : ⟨ X ⟩ → Type _
    ΣY x = Susp ⟨ Y x ⟩

  tr-merid : ∀ x → ⟨ Y x ⟩ → ∥ Path (ΣY x) north south ∥ (1 + j)
  tr-merid x = Tr.∣_∣ ∘ merid

  desuspension : Δ ℓ (suc j)
    → (∀ x → hasRetract (tr-merid x))
    → hasConnectedChoice (suc j) j X Y
  desuspension δ has-retr-tr-merid is-connected-Y = is-connected-ΠY where
    -- Suspension increases connectivity, so Σ(Y) is pointwise (1+j)-connected.
    is-connected-suc-ΣY : ∀ x → isConnected (1 + j) (ΣY x)
    is-connected-suc-ΣY x = isConnectedSusp j (is-connected-Y x)

    -- The familiar trick:
    -- Truncating the suspension of Y at level (2+j) preserves its connectivity at level (1+j),
    -- hence TrΣ(x) ≔ ∥ Σ(Y x) ∥₂₊ⱼ is a family of (1+j)-connected (2+j)-types.
    -- This means that Δ(1+j) applies to it, and that its sections are (1+j)-connected.
    TrΣ : ⟨ X ⟩ → TypeOfHLevel ℓ (2 + j)
    TrΣ x .fst = ∥ ΣY x ∥ (2 + j)
    TrΣ x .snd = Tr.isOfHLevelTrunc (2 + j)

    is-connected-suc-TrΣ : ∀ x → isConnected (1 + j) ⟨ TrΣ x ⟩
    is-connected-suc-TrΣ x = Connectivity.isConnected→isConnectedTruncPlus 1 (1 + j)
      $ is-connected-suc-ΣY x

    ΠTrΣ : Type _
    ΠTrΣ = ∀ x → ⟨ TrΣ x ⟩

    is-connected-suc-ΠTrΣ : isConnected (1 + j) ΠTrΣ
    is-connected-suc-ΠTrΣ = δ X TrΣ is-connected-suc-TrΣ

    -- There are two canonical sections of TrΣ: the truncations of north and south.
    -- (Written with explicit type annotations to highlight the dependency on the
    -- index x : X).
    tr-north tr-south : ΠTrΣ
    tr-north x = Tr.∣ the (ΣY x) north ∣
    tr-south x = Tr.∣ the (ΣY x) south ∣

    -- (1+j)-connectivity of TrΣ-sections means that, in particular,
    -- paths between `tr-north` and `tr-south` are j-connected.
    is-connected-merid-path : isConnected j (tr-north ≡ tr-south)
    is-connected-merid-path = isConnectedPath j is-connected-suc-ΠTrΣ tr-north tr-south

    -- We will show that sections of Y are a retract of `tr-north ≡ tr-south`, hence j-connected.
    -- First, we observe that the path type `tr-north ≡ tr-south` is equivalent to sections of a family
    -- of (1+j)-truncated paths; call them "meridians".
    TrMerid : ⟨ X ⟩ → Type _
    TrMerid x = ∥ Path (ΣY x) north south ∥ (1 + j)

    -- This follows from function extensionality and the characterization of paths in
    -- truncations: (1+j)-truncated paths are exactly paths in a (2+j)-truncation.
    tr-merid-equiv : (tr-north ≡ tr-south) ≃ (∀ x → TrMerid x)
    tr-merid-equiv =
      (tr-north ≡ tr-south)
        ≃⟨ invEquiv funExtEquiv ⟩
      (∀ x → Path (∥ ΣY x ∥ (2 + j)) Tr.∣ north ∣ Tr.∣ south ∣)
        ≃⟨ equivΠCod (λ x → isoToEquiv (Tr.PathIdTruncIso (1 + j))) ⟩
      (∀ x → ∥ Path (ΣY x) north south ∥ (1 + j))
        ≃∎

    -- Transporting across the equivalence, we conclude that sections of meridians are j-connected.
    is-connected-ΠTrMerid : isConnected j (∀ x → TrMerid x)
    is-connected-ΠTrMerid = Connectivity.isConnectedRespectEquiv j tr-merid-equiv is-connected-merid-path

    -- By assumption, Y is (pointwise) a retract of meridians.
    r : ∀ x → TrMerid x → ⟨ Y x ⟩
    r x = has-retr-tr-merid x .fst

    r-retract : ∀ x → retract (tr-merid x) (r x)
    r-retract x = has-retr-tr-merid x .snd

    -- This extends to sections: By function extensionality, Π(Y) is a retract of Π(TrMerid).
    r* : (∀ x → TrMerid x) → (∀ x → ⟨ Y x ⟩)
    r* p x = r x (p x)

    s* : (∀ x → ⟨ Y x ⟩) → (∀ x → TrMerid x)
    s* y x = tr-merid x (y x)

    r*-retract : retract s* r*
    r*-retract y = funExt λ x → r-retract x (y x)

    -- But we have already seen that Π(TrMerid) is j-connected, hence the same must hold for Π(Y).
    is-connected-ΠY : isConnected j (∀ x → ⟨ Y x ⟩)
    is-connected-ΠY = isConnectedRetract j s* r* r*-retract is-connected-ΠTrMerid

module Stable (j : HLevel) where
  private
    k : HLevel
    k = 3 + j

  stable : Δ ℓ (1 + k) → Δ ℓ k
  stable δ-suc X Y is-connected-Y = is-connected-ΠY where
    open Desuspension k X Y

    freudenthal-index-eq : j + (1 + k) ≡ ((2 + j) + (2 + j))
    freudenthal-index-eq = Nat.+-suc j (3 + j) ∙ cong suc (Nat.+-suc j (2 + j))

    module Pointwise (x : ⟨ X ⟩) where
      merid : (y : ⟨ Y x ⟩) → Path (Susp ⟨ Y x ⟩) Susp.north Susp.south
      merid = Susp.merid {A = ⟨ Y x ⟩}

      freudenthal : isConnectedFun ((2 + j) + (2 + j)) merid
      freudenthal = PT.rec Connectivity.isPropIsConnectedFun inh→is-conn-merid merely-inh-Y where
        merely-inh-Y : ∥ ⟨ Y x ⟩ ∥₁
        merely-inh-Y = Connectivity.isConnectedSuc→merelyInh (2 + j) (is-connected-Y x)

        inh→is-conn-merid : (y : ⟨ Y x ⟩) → isConnectedFun ((2 + j) + (2 + j)) merid
        inh→is-conn-merid y = isConnectedMerid (suc j) {A = ⟨ Y x ⟩ , y} (is-connected-Y x)

      is-conn-plus-merid : isConnectedFun (j + (1 + k)) merid
      is-conn-plus-merid = subst (λ - → isConnectedFun - merid) (sym freudenthal-index-eq)
        $ freudenthal

      is-conn-merid : isConnectedFun (1 + k) merid
      is-conn-merid = isConnectedFunSubtr (1 + k) j _ is-conn-plus-merid

      is-conn-∣-∣ : isConnectedFun (1 + k) (Tr.∣_∣ₕ {A = Path (Susp ⟨ Y x ⟩) Susp.north Susp.south} {n = 1 + k})
      is-conn-∣-∣ = Connectivity.isConnectedFunTrunc (1 + k)

      _ : tr-merid x ≡ Tr.∣_∣ₕ ∘ merid
      _ = refl

      is-conn-tr-merid : isConnectedFun (1 + k) (Tr.∣_∣ₕ ∘ merid)
      is-conn-tr-merid = isConnectedComp Tr.∣_∣ₕ merid (1 + k) is-conn-∣-∣ is-conn-merid

      is-equiv-tr-merid : isEquiv (tr-merid x)
      is-equiv-tr-merid = Connectivity.isConnectedFunOnTrunc→isEquiv (1 + k)
        is-conn-tr-merid
        (str $ Y x)
        (Tr.isOfHLevelTrunc (1 + k))

      has-retr-tr-merid : hasRetract (tr-merid x)
      has-retr-tr-merid .fst = invIsEq is-equiv-tr-merid
      has-retr-tr-merid .snd = retIsEq is-equiv-tr-merid

    is-connected-ΠY : isConnected k (∀ x → ⟨ Y x ⟩)
    is-connected-ΠY = desuspension δ-suc Pointwise.has-retr-tr-merid is-connected-Y

Δ[2]→DiscreteSetChoice : Δ ℓ 2 → DiscreteSetChoice ℓ
Δ[2]→DiscreteSetChoice δ X Y discrete-Y = invEq (hasSetChoice≃hasConnectedChoice[2,1] X Y) has-conn-choice where
  open Desuspension 1 X Y
  module ΣY x = Suspension.Code ⟨ Y x ⟩ (discrete-Y x)

  has-conn-choice : hasConnectedChoice 2 1 X Y
  has-conn-choice = desuspension δ ΣY.hasRetractTruncMerid

Δ[2]→LEM : Δ ℓ 2 → LEM ℓ
Δ[2]→LEM = discreteDiaconescu ∘ Δ[2]→DiscreteSetChoice

Δ[2]→Δ[1] : Δ ℓ 2 → Δ ℓ 1
Δ[2]→Δ[1] δ = equivFun ASC≃ACC[2,1] asc where
  open import Cubical.Relation.Nullary.Base using (Discrete)

  lem : LEM _
  lem = Δ[2]→LEM δ

  asc : ASC _ _
  asc X Y = Δ[2]→DiscreteSetChoice δ X Y discrete-Y where
    discrete-Y : ∀ x → Discrete ⟨ Y x ⟩
    discrete-Y x y₀ y₁ = lem $ the (hProp _) λ where
      .fst → y₀ ≡ y₁
      .snd → str (Y x) y₀ y₁
