module GpdCont.Axioms.ConnectedChoice where

open import GpdCont.Prelude
open import GpdCont.Connectivity as Connectivity
  using (merelyInh≃is1Connected ; isPropIsConnected ; isContr→isConnected ; isOfHLevel×isConnected→isContr)
open import GpdCont.Fibration
open import GpdCont.Axioms.TruncatedChoice

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso ; invIso ; section) renaming (_∎Iso to _Iso∎)
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties using (+-comm)
import Cubical.Data.Nat.Order as Nat≤
open import Cubical.Data.Sigma.Properties as Sigma
open import Cubical.HITs.Truncation as Tr using (∥_∥_)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level
    X Y : Type ℓ

-- The axiom of choice for sets can be generalized to higher h-levels in a different
-- direction to the one presented in the HoTT book by considering connectivity:

-- The axiom of (set) choice holds whenever a family of 1-connected sets has a
-- 1-connected type of (global) sections.
-- The reason for that is that being 1-connected means having contractible
-- propostional truncation — which is the case as soon as the truncation is inhabited.
_ : ASC ℓ ℓ ≃ ∀ (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) → ((x : ⟨ X ⟩) → isConnected 1 ⟨ Y x ⟩) → isConnected 1 ((x : ⟨ X ⟩) → ⟨ Y x ⟩)
_ = equivΠCod λ X → equivΠCod λ Y → equiv→ (equivΠCod (λ x → merelyInh≃is1Connected)) merelyInh≃is1Connected

-- We say that a family of n-types (indexed by a set) has "k-connected choice" iff
-- it being pointwise k-connected implies it having a k-connected type of (global) sections.
--
-- In the following, we use this convention for h-levels:
-- · n - indexes n-types
-- · k - defines a level of (k)onnectivity
hasConnectedChoice : (n k : HLevel) (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ n) → Type _
hasConnectedChoice n k X Y = ((x : ⟨ X ⟩) → isConnected k ⟨ Y x ⟩) → isConnected k ((x : ⟨ X ⟩) → ⟨ Y x ⟩)

-- As opposed to [hasChoice m n] above, having k-connected choice is a proposition:
isPropHasConnectedChoice : ∀ {n} (k : HLevel) (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ n) → isProp (hasConnectedChoice n k X Y)
isPropHasConnectedChoice _ _ _ = isPropΠ λ _ → isPropIsConnected

-- We turn this into an axiom:
-- The n-th axiom of k-connected choice says that all families of n-types satisfy k-connected choice.
ACC : (ℓ : Level) (n k : HLevel) → Type _
ACC ℓ n k = ∀ (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ n) → hasConnectedChoice n k X Y

-- Again, this is a proposition, whereas AC(m, n) is not:
isPropACC : ∀ {ℓ} (n k : HLevel) → isProp (ACC ℓ n k)
isPropACC n k = isPropΠ2 λ X Y → isPropHasConnectedChoice k X Y

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

ACC[+1,+1]→ACC : (n k : HLevel) → ACC ℓ (suc n) (suc k) → ACC ℓ n k
ACC[+1,+1]→ACC n k acc-suc X Y conn-Y = {!acc-suc _ _ _ !}

ACC→ACC[+1,+1] : (n k : HLevel) → ACC ℓ n k → ACC ℓ (suc n) (suc k)
ACC→ACC[+1,+1] n k acc X Y conn-Y = {!acc _ _ _ !}

-- Being "split" can similarly be generalized to higher h-levels:
-- A function is k-split if it has an k-connected type of sections.
isConnectedHasSection : (k : HLevel) (f : X → Y) → Type _
isConnectedHasSection k f = isConnected k (hasSection f)

foo : (k : HLevel) (f : X → Y) → isConnectedHasSection k f ≃ isConnected k (Σ[ g ∈ (Y → X) ] (∀ y → f (g y) ≡ y))
foo k f = {! !}

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

CFCSSuc→CFCS : (n k : HLevel) → ConnectedFunsHaveConnectedSections ℓ (suc n) (suc k) → ConnectedFunsHaveConnectedSections ℓ n k
CFCSSuc→CFCS n k cfcs-suc X Y f k-conn-f = {! !}


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

ACC[n,-]→ACC[n,suc-] : (n k : HLevel) → ACC ℓ n k → ACC ℓ n (suc k)
ACC[n,-]→ACC[n,suc-] n k acc X Y conn-Y = is-suc-connected-section where
  ΠY : Type _
  ΠY = ∀ x → ⟨ Y x ⟩

  _≡Π_ : (f g : ΠY) → Type _
  _≡Π_ f g = ∀ x → f x ≡ g x

  SIP-Π : ∀ {f g} → (f ≡ g) ≃ (f ≡Π g)
  SIP-Π = invEquiv funExtEquiv

  isOfHLevel-≡Π : (f g : ΠY) → ∀ x → isOfHLevel n (f x ≡ g x)
  isOfHLevel-≡Π f g x = isOfHLevelPath n (str (Y x)) (f x) (g x)

  inh-trunc×conn-Y : ∀ x → ∥ ⟨ Y x ⟩ ∥ (suc k) × ∀ (y y′ : ⟨ Y x ⟩) → isConnected k (y ≡ y′)
  inh-trunc×conn-Y x = (invEq $ Connectivity.inhTruncSuc×isConnectedPath≃isConnectedSuc k) $ (conn-Y x)

  inh-trunc : ∀ x → ∥ ⟨ Y x ⟩ ∥ (suc k)
  inh-trunc x = inh-trunc×conn-Y x .fst

  is-k-conn-Path-Y : ∀ x (y y′ : ⟨ Y x ⟩) → isConnected k (y ≡ y′)
  is-k-conn-Path-Y x = inh-trunc×conn-Y x .snd

  inh-trunc-Π : ∥ (∀ x → ⟨ Y x ⟩) ∥ (suc k)
  inh-trunc-Π = {!  !}

  is-connected-≡Π : ∀ f g → isConnected k (f ≡Π g)
  is-connected-≡Π f g = acc X
    (λ x → (f x ≡ g x) , isOfHLevel-≡Π f g x)
    (λ x → isConnectedPath k (conn-Y x) (f x) (g x))

  is-connected-path : ∀ (f g : ∀ x → ⟨ Y x ⟩) → isConnected k (f ≡ g)
  is-connected-path f g = isConnectedRetractFromIso k (equivToIso SIP-Π) (is-connected-≡Π f g)

  is-suc-connected-section : isConnected (suc k) (∀ x → ⟨ Y x ⟩)
  is-suc-connected-section = Connectivity.inhTruncSuc×isConnectedPath→isConnectedSuc k
    inh-trunc-Π
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

