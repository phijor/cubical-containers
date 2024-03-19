module GpdCont.Axiom where

open import GpdCont.Prelude
open import GpdCont.Connectivity using (merelyInh≃is1Connected ; isPropIsConnected ; isContr→isConnected)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (isEquiv→isContrHasSection) renaming (hasSection to Section)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso ; invIso ; section ; _Iso⟨_⟩_) renaming (_∎Iso to _Iso∎)
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties as Nat using (max)
import Cubical.Data.Nat.Order as Nat≤
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties as Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.Truncation as Tr using (∥_∥_)
open import Cubical.HITs.Nullification.Base using (∣_∣)
open import Cubical.Functions.Surjection
open import Cubical.Functions.Fibration
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level
    X Y : Type ℓ

Section-fiber-Iso : (f : X → Y) → Iso (Section f) (∀ (y : Y) → fiber f y)
Section-fiber-Iso f = invIso Sigma.Σ-Π-Iso

private
  Σ-contractSndIso : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} → ((a : A) → isContr (B a)) → Iso (Σ A B) A
  Σ-contractSndIso c = isom
    where
    isom : Iso _ _
    isom .Iso.fun = fst
    isom .Iso.inv a = a , c a .fst
    isom .Iso.rightInv _ = refl
    isom .Iso.leftInv (a , b) = cong (a ,_) (c a .snd b)

module Total (X : Type ℓ) (Y : X → Type ℓ) where
  Total : Type _
  Total = Σ[ x ∈ X ] (Y x)

  isOfHLevelTotal : ∀ n → isOfHLevel n X → (∀ x → isOfHLevel n (Y x)) → isOfHLevel n Total
  isOfHLevelTotal = isOfHLevelΣ

  proj : Total → X
  proj = fst

  isSetBase→isOfHLevelTotal : ∀ (n : HLevel) → isSet X → (∀ x → isOfHLevel n (Y x)) → isOfHLevel (max 2 n) Total
  isSetBase→isOfHLevelTotal 0 is-set-X is-contr-Y = isOfHLevelRetractFromIso 2 (Σ-contractSndIso is-contr-Y) is-set-X
  isSetBase→isOfHLevelTotal 1 is-set-X is-prop-Y = λ t t′ → isOfHLevelRespectEquiv 1 (Σ≡PropEquiv is-prop-Y) (is-set-X (proj t) (proj t′))
  isSetBase→isOfHLevelTotal (suc (suc n)) is-set-X = isOfHLevelΣ (2 + n) (isOfHLevelPlus' {n = n} 2 is-set-X)

  Section→Family : Section proj → (∀ x → Y x)
  Section→Family (ι , sect-ι) x = subst Y (sect-ι x) (ι x .snd)

  Family→Section : (∀ x → Y x) → Section proj
  Family→Section s = (λ x → x , s x) , λ x → refl

  Section-Family-Iso : Iso (Section proj) (∀ x → Y x)
  Section-Family-Iso .Iso.fun = Section→Family
  Section-Family-Iso .Iso.inv = Family→Section
  Section-Family-Iso .Iso.rightInv s = funExt λ x → substRefl {B = Y} (s x)
  Section-Family-Iso .Iso.leftInv (ι , sect-ι) = sym left-inv where
    left-inv : (ι , sect-ι) ≡ Family→Section (Section→Family (ι , sect-ι))
    left-inv i .fst x .fst = sect-ι x i
    left-inv i .fst x .snd = subst-filler Y (sect-ι x) (ι x .snd) i
    left-inv i .snd x j = sect-ι x (i ∨ j)

  fiber-proj→Family : ∀ x → fiber proj x → Y x
  fiber-proj→Family x ((x′ , y′) , p) = subst Y p y′

  Family→fiber-proj : ∀ x → Y x → fiber proj x
  Family→fiber-proj x y .fst = x , y
  Family→fiber-proj x y .snd = refl

  -- This is essentially contractibility of singletons around x:
  proj-fiber-Iso : ∀ x → Iso (fiber proj x) (Y x)
  proj-fiber-Iso x .Iso.fun = fiber-proj→Family x
  proj-fiber-Iso x .Iso.inv = Family→fiber-proj x
  proj-fiber-Iso x .Iso.rightInv y = substRefl {B = Y} y
  proj-fiber-Iso x .Iso.leftInv t@((x′ , y′) , p) = sym left-inv where
    left-inv : t ≡ Family→fiber-proj x (fiber-proj→Family x t)
    left-inv i .fst .fst = p i
    left-inv i .fst .snd = subst-filler Y p y′ i
    left-inv i .snd j = p (i ∨ j)

-- A family of n-types has m-choice iff
--  "the family is pointwise m-inhabited"
-- implies
--  "the family has an m-truncated section"
hasChoice : (n m : HLevel) (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ n) → Type _
hasChoice n m X Y = ((x : ⟨ X ⟩) → ∥ ⟨ Y x ⟩ ∥ m) → ∥ ((x : ⟨ X ⟩) → ⟨ Y x ⟩) ∥ m

isOfHLevelHasChoice : ∀ {n} (m : HLevel) (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ n) → isOfHLevel m (hasChoice n m X Y)
isOfHLevelHasChoice m _ _ = isOfHLevelΠ m λ _ → Tr.isOfHLevelTrunc m

-- The (n,m) axiom of choice says that all families of n-types
-- have m-truncated sections whenever they are pointwise m-inhabited.
AC : (ℓ : Level) (n m : HLevel) → Type _
AC ℓ n m = ∀ (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ n) → hasChoice n m X Y

-- The usual axiom of choice: Merely (1-) inhabited families merely have sections.
hasSetChoice : (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) → Type _
hasSetChoice X Y = ((x : ⟨ X ⟩) → ∥ ⟨ Y x ⟩ ∥₁) → ∥ ((x : ⟨ X ⟩) → ⟨ Y x ⟩) ∥₁

AC₂₁ : (ℓ : Level) → Type _
AC₂₁ ℓ = ∀ (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) → hasSetChoice X Y

isPropHasChoice : (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) → isProp (hasSetChoice X Y)
isPropHasChoice _ _ = isPropΠ λ _ → PT.isPropPropTrunc

hasChoice₂₁≃hasSetChoice : ∀ (X : hSet ℓ) Y → hasSetChoice X Y ≃ hasChoice 2 1 X Y
hasChoice₂₁≃hasSetChoice X Y = equiv→ (equivΠCod λ x → Tr.propTrunc≃Trunc1) Tr.propTrunc≃Trunc1

-- A functions is split if it merely has a section.
isSplit : (f : X → Y) → Type _
isSplit {X} {Y} f = ∃[ g ∈ (Y → X) ] section f g

-- The classical axiom that every surjection between sets splits:
AllSurjectionsSplit : (ℓ : Level) → Type _
AllSurjectionsSplit ℓ = ∀ (X Y : hSet ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) → isSurjection f → isSplit f

-- If we assume choice for the fibers of a function of sets,
-- then the function splits if it is a surjection.
module FiberChoice (X Y : hSet ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) where
  fiberSet : (y : ⟨ Y ⟩) → hSet _
  fiberSet y .fst = fiber f y
  fiberSet y .snd = isSetΣ (str X) λ x → isProp→isSet (str Y (f x) y)

  hasChoiceFiber→isSplitSurjection : hasSetChoice Y fiberSet → (isSurjection f → isSplit f)
  hasChoiceFiber→isSplitSurjection choice-fiber-f surj-f = goal where
    goal : isSplit f
    goal = PT.map (Section-fiber-Iso f .Iso.inv) (choice-fiber-f surj-f)

-- The axiom of choice implies that all surjections split.
AC₂₁→AllSurjectionsSplit : AC₂₁ ℓ → AllSurjectionsSplit ℓ
AC₂₁→AllSurjectionsSplit ac X Y f = hasChoiceFiber→isSplitSurjection has-set-choice where
  open FiberChoice X Y f using (hasChoiceFiber→isSplitSurjection ; fiberSet)

  has-set-choice : hasSetChoice Y fiberSet
  has-set-choice = ac Y fiberSet

-- For any family, the total space over the family comes with a canonical fibration
-- over the domain of the family.
--
-- If the projection splits whenever it is a surjection, then choice holds for the family.
module TotalFibration (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) where
  module T = Total ⟨ X ⟩ (⟨_⟩ ∘ Y)
  open T using (proj) public
  open T using (Total)

  TotalSet : hSet _
  TotalSet .fst = Total
  TotalSet .snd = T.isOfHLevelTotal 2 (str X) (str ∘ Y)

  surjectiveProjSplits→hasChoice : (isSurjection proj → isSplit proj) → hasSetChoice X Y
  surjectiveProjSplits→hasChoice proj-surj→split mere-inh-fam = goal where
    is-surjection-proj : isSurjection proj
    is-surjection-proj x = PT.map (T.proj-fiber-Iso x .Iso.inv) (mere-inh-fam x)

    goal : ∥ (∀ x → ⟨ Y x ⟩) ∥₁
    goal = PT.map (T.Section-Family-Iso .Iso.fun) $ proj-surj→split is-surjection-proj

-- If all surjections between sets split, then the axiom of choice holds.
AllSurjectionsSplit→AC₂₁ : AllSurjectionsSplit ℓ → AC₂₁ ℓ
AllSurjectionsSplit→AC₂₁ split X Y = surjectiveProjSplits→hasChoice is-surj→is-split where
  open TotalFibration X Y using (TotalSet ; proj ; surjectiveProjSplits→hasChoice)
  is-surj→is-split : isSurjection proj → isSplit proj
  is-surj→is-split = split TotalSet X proj

-- The axiom of choice for sets can be generalized to higher h-levels in a different
-- direction to the one presented in the HoTT book by considering connectivity:

-- The axiom of (set) choice holds whenever a family of 1-connected sets has a
-- 1-connected type of (global) sections.
-- The reason for that is that being 1-connected means having contractible
-- propostional truncation — which is the case as soon as the truncation is inhabited.
_ : AC₂₁ ℓ ≃ ∀ (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ) → ((x : ⟨ X ⟩) → isConnected 1 ⟨ Y x ⟩) → isConnected 1 ((x : ⟨ X ⟩) → ⟨ Y x ⟩)
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

-- Similarly, being "split" can be generalized to higher h-levels:
-- A function is k-split if it has an k-connected type of sections.
hasConnectedSections : (k : HLevel) (f : X → Y) → Type _
hasConnectedSections k f = isConnected k (Section f)

-- This too is a proposition, again because "being connected" is a proposition:
isPropHasConnectedSections : (k : HLevel) (f : X → Y) → isProp (hasConnectedSections k f)
isPropHasConnectedSections k f = isPropIsConnected

-- For n=1 the two notions coincide:
--
-- Being split (= merely having a section) is the same as having a 1-connected type of sections.
isSplit≃has1ConnectedSections : {f : X → Y} → isSplit f ≃ hasConnectedSections 1 f
isSplit≃has1ConnectedSections = merelyInh≃is1Connected

-- We turn "every surjection between sets has a section" into its analogue for higher
-- h-levels and notions of connectivity:
--
-- Axiom: Every k-connected map from an n-type onto a set has a k-connected space of sections.
ConnectedFunsHaveConnectedSections : (ℓ : Level) (n k : HLevel) → Type _
ConnectedFunsHaveConnectedSections ℓ n k = ∀ (X : TypeOfHLevel ℓ n) (Y : hSet ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) → isConnectedFun k f → hasConnectedSections k f

isPropConnectedFunsHaveConnectedSections : ∀ {ℓ} (n k : HLevel) → isProp (ConnectedFunsHaveConnectedSections ℓ n k)
isPropConnectedFunsHaveConnectedSections n k = isPropΠ4 λ X Y f conn → isPropHasConnectedSections k f

isSurjection≃is1ConnectedFun : ∀ {X Y : Type ℓ} (f : X → Y) → isSurjection f ≃ isConnectedFun 1 f
isSurjection≃is1ConnectedFun f = equivΠCod λ b → merelyInh≃is1Connected

-- Consistency check: All surjections split iff 1-connected maps between sets have 1-connected sections.
AllSurjectionsSplit≃ConnectedFunsHaveConnectedSections₂₁ : AllSurjectionsSplit ℓ ≃ ConnectedFunsHaveConnectedSections ℓ 2 1
AllSurjectionsSplit≃ConnectedFunsHaveConnectedSections₂₁ =
  equivΠCod λ X → equivΠCod λ Y → equivΠCod λ f → equiv→ (isSurjection≃is1ConnectedFun f) (isSplit≃has1ConnectedSections {f = f})

-- ACC implies that connected functions have connected sections.
--
-- Proof.  Consider the family of fibers of a function:
-- Assuming connected choice for this family, we can turn the statement
--  "f is k-connected" (≃ "f has k-connected fibers")
-- into
--  "global sections of the fibers of f are k-connected".
-- But these global sections are exactly the (usual) sections of f,
-- therefore these are k-connected too.
module FiberConnectivity {n : HLevel} (X : TypeOfHLevel ℓ (suc n)) (Y : hSet ℓ) (f : ⟨ X ⟩ → ⟨ Y ⟩) where
  private
    n⁺ = suc n

  fiberOfHLevel : (y : ⟨ Y ⟩) → TypeOfHLevel ℓ n⁺
  fiberOfHLevel y .fst = fiber f y
  fiberOfHLevel y .snd = isOfHLevelΣ n⁺ (str X) λ x → isProp→isOfHLevelSuc n (str Y (f x) y)

  hasConnectedChoiceFiber→hasConnectedSections : (k : HLevel) → hasConnectedChoice n⁺ k Y fiberOfHLevel → (isConnectedFun k f → hasConnectedSections k f)
  hasConnectedChoiceFiber→hasConnectedSections k conn-choice conn-f = goal where
    -- Connected choice says that global sections of `fiber f` are k-connected:
    hasConnectedFiberSections : isConnected k (∀ y → fiber f y)
    hasConnectedFiberSections = conn-choice conn-f

    Section-f-global-section-fiber-Iso : Iso (Section f) (∀ y → fiber f y)
    Section-f-global-section-fiber-Iso = Section-fiber-Iso f

    goal : hasConnectedSections k f
    goal = isConnectedRetractFromIso k Section-f-global-section-fiber-Iso hasConnectedFiberSections

ACC→ConnectedFunsHaveConnectedSections-[1+_,_] : (n k : HLevel) → ACC ℓ (suc n) k → ConnectedFunsHaveConnectedSections ℓ (suc n) k
ACC→ConnectedFunsHaveConnectedSections-[1+_,_] n k conn-choice X Y f conn-f = F.hasConnectedChoiceFiber→hasConnectedSections k (conn-choice Y F.fiberOfHLevel) conn-f where
  module F = FiberConnectivity X Y f


ConnectedFunsHaveConnectedSections[0,0] : ConnectedFunsHaveConnectedSections ℓ 0 0
ConnectedFunsHaveConnectedSections[0,0] X Y f _ = isConnectedZero (Section f)

ConnectedFunsHaveConnectedSections[0,1+_] : ∀ k → ConnectedFunsHaveConnectedSections ℓ 0 (suc k)
ConnectedFunsHaveConnectedSections[0,1+ k ] X Y f conn-f = hasConnectedSections-f where
  x₀ : ⟨ X ⟩
  x₀ = str X .fst

  one-inh-fiber : ∀ y → fiber f y → f x₀ ≡ y
  one-inh-fiber y (x , p) = cong f (str X .snd x) ∙ p

  1-conn-f : isConnectedFun 1 f
  1-conn-f = isConnectedFun≤ 1 (suc k) f (Nat≤.suc-≤-suc Nat≤.zero-≤) conn-f

  inh-fib : ∀ y → ∥ fiber f y ∥ 1
  inh-fib y = 1-conn-f y .fst

  isSet-Y : isSet ⟨ Y ⟩
  isSet-Y = str Y

  sec-f-const : section f (const x₀)
  sec-f-const y = Tr.rec₊ {B = f x₀ ≡ y} (isSet-Y (f x₀) y) (one-inh-fiber y) (inh-fib y)

  section-f-equiv : Section f ≃ (∀ y → f x₀ ≡ y)
  section-f-equiv =
    Section f ≃⟨⟩
    Σ[ g ∈ (⟨ Y ⟩ → ⟨ X ⟩) ] section f g ≃⟨ Σ-contractFst (isContrΠ λ _ → str X) ⟩
    section f (const x₀) ≃⟨⟩
    (∀ y → f x₀ ≡ y) ≃∎

  isPropSection-f : isProp (Section f)
  isPropSection-f = isOfHLevelRespectEquiv 1 (invEquiv section-f-equiv) (isPropΠ λ y → isSet-Y (f x₀) y)

  ∃!-section-f : isContr (Section f)
  ∃!-section-f = inhProp→isContr (const x₀ , sec-f-const) isPropSection-f

  hasConnectedSections-f : isConnected (suc k) (Section f)
  hasConnectedSections-f = isContr→isConnected (suc k) ∃!-section-f

ACC→ConnectedFunsHaveConnectedSections-[0,_] : (k : HLevel) → ACC ℓ 0 k → ConnectedFunsHaveConnectedSections ℓ 0 k
ACC→ConnectedFunsHaveConnectedSections-[0, 0 ] _ = ConnectedFunsHaveConnectedSections[0,0]
ACC→ConnectedFunsHaveConnectedSections-[0, (suc k) ] _ = ConnectedFunsHaveConnectedSections[0,1+ k ]

ACC→ConnectedFunsHaveConnectedSections : (n k : HLevel) → ACC ℓ n k → ConnectedFunsHaveConnectedSections ℓ n k
ACC→ConnectedFunsHaveConnectedSections zero k = ACC→ConnectedFunsHaveConnectedSections-[0, k ]
ACC→ConnectedFunsHaveConnectedSections (suc n) k = ACC→ConnectedFunsHaveConnectedSections-[1+ n , k ]

-- If connected functions have connected sections, then ACC holds.
--
-- Proof.  Consider the total fibration `proj : Σ X Y → X`.
-- If Y is pointwise k-connected, then proj is a k-connected function.
-- Using our assumption, we can conclude that proj has k-connected sections.
-- But the sections of proj are exactly the global sections of Y, thus global
-- sections of Y are k-connected.
module TotalFibrationConnectivity {n : HLevel} (X : hSet ℓ) (Y : ⟨ X ⟩ → TypeOfHLevel ℓ (2 + n)) where
  module T = Total ⟨ X ⟩ (⟨_⟩ ∘ Y)

  open T using (proj) public
  open T using (Total ; isOfHLevelTotal ; proj ; Section-Family-Iso ; proj-fiber-Iso)

  TotalOfHLevel : TypeOfHLevel ℓ (2 + n)
  TotalOfHLevel .fst = Total
  TotalOfHLevel .snd = isOfHLevelTotal (2 + n) (isOfHLevelPlus' 2 (str X)) (str ∘ Y)

  isConnectedFam→isConnectedFunProj : ∀ k → (∀ x → isConnected k ⟨ Y x ⟩) → isConnectedFun k proj
  isConnectedFam→isConnectedFunProj k conn-fam x = conn-fibers where
    conn-fibers : isConnected k (fiber proj x)
    conn-fibers = isConnectedRetractFromIso k (proj-fiber-Iso x) (conn-fam x)

  hasConnectedSections→hasConnectedChoiceFiber : (k : HLevel) → (isConnectedFun k proj → hasConnectedSections k proj) → hasConnectedChoice (2 + n) k X Y
  hasConnectedSections→hasConnectedChoiceFiber k conn-proj→conn-sec-proj conn-fam = isConnectedFam where
    isConnectedFunProj : isConnectedFun k proj
    isConnectedFunProj = isConnectedFam→isConnectedFunProj k conn-fam

    hasConnectedSectionsProj : hasConnectedSections k proj
    hasConnectedSectionsProj = conn-proj→conn-sec-proj isConnectedFunProj

    global-section-Section-proj-Iso : Iso (∀ x → ⟨ Y x ⟩) (Section proj)
    global-section-Section-proj-Iso = invIso Section-Family-Iso

    isConnectedFam : isConnected k (∀ x → ⟨ Y x ⟩)
    isConnectedFam = isConnectedRetractFromIso k global-section-Section-proj-Iso hasConnectedSectionsProj

ConnectedFunsHaveConnectedSections→ACC-[2+_,_] : (n k : HLevel) → ConnectedFunsHaveConnectedSections ℓ (2 + n) k → ACC ℓ (2 + n) k
ConnectedFunsHaveConnectedSections→ACC-[2+_,_] n k conn-fun→conn-sec X Y = F.hasConnectedSections→hasConnectedChoiceFiber k (conn-fun→conn-sec F.TotalOfHLevel X F.proj) where
  module F = TotalFibrationConnectivity X Y

ACC[0,_] : (k : HLevel) → ACC ℓ 0 k
ACC[0, k ] X Y = hasConnectedChoice₀ where
  hasConnectedChoice₀ : ((x : ⟨ X ⟩) → isConnected k ⟨ Y x ⟩) → isConnected k ((x : ⟨ X ⟩) → ⟨ Y x ⟩)
  hasConnectedChoice₀ unused-assumption = isContr→isConnected k (isContrΠ (str ∘ Y))

ACC[_,0] : (n : HLevel) → ACC ℓ n 0
ACC[ n ,0] X Y _ = isConnectedZero (∀ x → ⟨ Y x ⟩)

ConnectedFunsHaveConnectedSections→ACC-[0,_] : (k : HLevel) → ConnectedFunsHaveConnectedSections ℓ 0 k → ACC ℓ 0 k
ConnectedFunsHaveConnectedSections→ACC-[0,_] k unused-conn-fun→conn-sec = ACC[0, k ]

ConnectedFunsHaveConnectedSections→ACC-[1,0] : ConnectedFunsHaveConnectedSections ℓ 1 0 → ACC ℓ 1 0
ConnectedFunsHaveConnectedSections→ACC-[1,0] conn-fun→conn-sec X Y _ = isConnectedZero (∀ x → ⟨ Y x ⟩)

ACC[1,1+_] : (k : HLevel) → ACC ℓ 1 (suc k)
ACC[1,1+ k ] X Y = 1+k-connectedSection where
  isProp-Y : ∀ x → isProp ⟨ Y x ⟩
  isProp-Y = str ∘ Y

  module _ (conn-Y : ∀ x → isConnected (suc k) ⟨ Y x ⟩) where
    clue : ∀ x → ∥ ⟨ Y x ⟩ ∥ suc k ≃ ⟨ Y x ⟩
    clue x = Tr.truncIdempotent≃ (suc k) (isProp→isOfHLevelSuc k $ isProp-Y x)

    sec : ∀ x → ⟨ Y x ⟩
    sec x = equivFun (clue x) ∣y∣ where
      ∣y∣ : ∥ ⟨ Y x ⟩ ∥ (suc k)
      ∣y∣ = conn-Y x .fst

    isContr-Sections : isContr (∀ x → ⟨ Y x ⟩)
    isContr-Sections = inhProp→isContr sec (isPropΠ isProp-Y)

    1+k-connectedSection : isConnected (suc k) ((x : ⟨ X ⟩) → ⟨ Y x ⟩)
    1+k-connectedSection = isContr→isConnected (suc k) isContr-Sections


ConnectedFunsHaveConnectedSections→ACC-[1,1+_] : (k : HLevel) → ConnectedFunsHaveConnectedSections ℓ 1 (suc k) → ACC ℓ 1 (suc k)
ConnectedFunsHaveConnectedSections→ACC-[1,1+_] k _ = ACC[1,1+ k ]

ConnectedFunsHaveConnectedSections→ACC-[1,_] : (k : HLevel) → ConnectedFunsHaveConnectedSections ℓ 1 k → ACC ℓ 1 k
ConnectedFunsHaveConnectedSections→ACC-[1, zero ] = ConnectedFunsHaveConnectedSections→ACC-[1,0]
ConnectedFunsHaveConnectedSections→ACC-[1, suc k ] = ConnectedFunsHaveConnectedSections→ACC-[1,1+ k ]

ConnectedFunsHaveConnectedSections→ACC : (n k : HLevel) → ConnectedFunsHaveConnectedSections ℓ n k → ACC ℓ n k
ConnectedFunsHaveConnectedSections→ACC 0 = ConnectedFunsHaveConnectedSections→ACC-[0,_]
ConnectedFunsHaveConnectedSections→ACC 1 = ConnectedFunsHaveConnectedSections→ACC-[1,_]
ConnectedFunsHaveConnectedSections→ACC (suc (suc n)) k = ConnectedFunsHaveConnectedSections→ACC-[2+ n , k ]

-- Theorem: ACC(n,k) is equivalent to all k-connected functions having k-connected sections.
ACC≃ConnectedFunsHaveConnectedSections : (n k : HLevel) → ACC ℓ n k ≃ ConnectedFunsHaveConnectedSections ℓ n k
ACC≃ConnectedFunsHaveConnectedSections n k = propBiimpl→Equiv
  (isPropACC n k)
  (isPropConnectedFunsHaveConnectedSections n k)
  (ACC→ConnectedFunsHaveConnectedSections n k)
  (ConnectedFunsHaveConnectedSections→ACC n k)
