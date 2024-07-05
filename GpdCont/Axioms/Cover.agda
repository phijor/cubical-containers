{- The axiom of n-type covers.
-- https://ncatlab.org/nlab/show/n-types+cover#in_homotopy_type_theory
-}
module GpdCont.Axioms.Cover where

open import GpdCont.Prelude
open import GpdCont.SetTruncation using (isSurjection-∣-∣₂ ; isConnected-fiber-∣-∣₂)
open import GpdCont.Axioms.TruncatedChoice
open import GpdCont.Axioms.ConnectedChoice
  renaming
  ( ConnectedFunsHaveConnectedSections to CFCS
  ; isPropConnectedFunsHaveConnectedSections to isPropCFCS
  )
open import GpdCont.Connectivity

open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv using (propBiimpl→Equiv)
open import Cubical.Foundations.Equiv.Properties using (hasSection)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Surjection
open import Cubical.Data.Sigma
open import Cubical.Data.Nat as Nat using ()
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.Truncation as Tr using (∥_∥_)
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level
    n : HLevel

hasCover : ∀ {ℓ} (n : HLevel) (X : Type ℓ) → Type (ℓ-suc ℓ)
hasCover {ℓ} n X = ∃[ Y ∈ TypeOfHLevel ℓ n ] ⟨ Y ⟩ ↠ X

isPropHasCover : (n : HLevel) (X : Type ℓ) → isProp (hasCover n X)
isPropHasCover n X = PT.isPropPropTrunc

EnoughTypesOfHLevel : (ℓ : Level) (n : HLevel) → Type (ℓ-suc ℓ)
EnoughTypesOfHLevel ℓ n = ∀ X → hasCover {ℓ} n X

isPropEnoughTypesOfHLevel : (n : HLevel) → isProp (EnoughTypesOfHLevel ℓ n)
isPropEnoughTypesOfHLevel n = isPropΠ (isPropHasCover n)

EnoughSets : (ℓ : Level) → Type (ℓ-suc ℓ)
EnoughSets ℓ = EnoughTypesOfHLevel ℓ 2

isPropEnoughSets : isProp (EnoughSets ℓ)
isPropEnoughSets = isPropEnoughTypesOfHLevel 2

AllSurjectionsSplitω : (ℓ : Level) → Type _
AllSurjectionsSplitω ℓ = ∀ (X : Type ℓ) → (Y : hSet ℓ) (f : X → ⟨ Y ⟩) → isSurjection f → isSplit f

isPropAllSurjectionsSplitω : isProp (AllSurjectionsSplitω ℓ)
isPropAllSurjectionsSplitω = isPropΠ4 λ { _ _ f _ → isPropIsSplit f }

AllSurjectionsSplitω→AllSurjectionsSplit : AllSurjectionsSplitω ℓ → AllSurjectionsSplit ℓ
AllSurjectionsSplitω→AllSurjectionsSplit split X = split ⟨ X ⟩

isPathConnected→isSurjectionSection : ∀ {X Y : Type ℓ} → (f : X → Y)
  → isPathConnectedFun f
  → {g : Y → X}
  → section f g
  → isSurjection g
isPathConnected→isSurjectionSection f conn-f {g} sect x = goal where
  fiber-f : Type _
  fiber-f = fiber f (f x)

  mere-paths : (a b : fiber-f) → ∥ a ≡ b ∥₁
  mere-paths = isPathConnected→merePath (conn-f (f x))

  fib-gf : fiber-f
  fib-gf .fst = g (f x)
  fib-gf .snd = sect (f x)

  fib-x : fiber-f
  fib-x .fst = x
  fib-x .snd = refl

  goal : ∥ fiber g x ∥₁
  goal = PT.map (λ (p : fib-gf ≡ fib-x) → f x , cong fst p) $ mere-paths fib-gf fib-x

AllSurjectionsSplitω→EnoughSets : AllSurjectionsSplitω ℓ → EnoughSets ℓ
AllSurjectionsSplitω→EnoughSets split-ω X = hasSetCover where
  ∥X∥₂ : hSet _
  ∥X∥₂ = ST.∥ X ∥₂ , ST.isSetSetTrunc

  ∣-∣₂-section : ∥ hasSection ∣_∣₂ ∥₁
  ∣-∣₂-section = split-ω X ∥X∥₂ ∣_∣₂ (isSurjection-∣-∣₂ X)

  hasSetCover : hasCover 2 X
  hasSetCover = PT.map (λ { (pt , sect) → ∥X∥₂ , (pt , isPathConnected→isSurjectionSection ∣_∣₂ isConnected-fiber-∣-∣₂ sect) }) ∣-∣₂-section

AllSurjectionsSplit→EnoughSets→AllSurjectionsSplitω : AllSurjectionsSplit ℓ → EnoughSets ℓ → AllSurjectionsSplitω ℓ
AllSurjectionsSplit→EnoughSets→AllSurjectionsSplitω {ℓ} split sets-cover X Z f surj-f = goal where
  has-cover : ∃[ Y ∈ hSet _ ] ⟨ Y ⟩ ↠ X
  has-cover = sets-cover X

  under-cover : (Σ[ Y ∈ hSet _ ] (⟨ Y ⟩ ↠ X)) → isSplit f
  under-cover (Y , h) = PT.map (λ { (u , sect-u) → h .fst ∘ u , sect-u }) split-it where
    f∘h : ⟨ Y ⟩ ↠ ⟨ Z ⟩
    f∘h = compSurjection h (f , surj-f)

    split-it : isSplit (f∘h .fst)
    split-it = split Y Z _ (f∘h .snd)

  goal : isSplit f
  goal = PT.elim (λ _ → PT.isPropPropTrunc) under-cover has-cover

AllSurjectionsSplit×EnoughSets≃AllSurjectionsSplitω : (AllSurjectionsSplit ℓ × EnoughSets ℓ) ≃ AllSurjectionsSplitω ℓ
AllSurjectionsSplit×EnoughSets≃AllSurjectionsSplitω = propBiimpl→Equiv
  (isProp× isPropAllSurjectionsSplit isPropEnoughSets)
  isPropAllSurjectionsSplitω
  (uncurry AllSurjectionsSplit→EnoughSets→AllSurjectionsSplitω)
  λ where
    split-ω .fst → AllSurjectionsSplitω→AllSurjectionsSplit split-ω
    split-ω .snd → AllSurjectionsSplitω→EnoughSets split-ω


--------

record ConnectedCover {ℓ} (n k : HLevel) (X : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    Cover : Type ℓ
    cover-map : Cover → X
    is-truncated-cover : isOfHLevel n Cover
    is-connected-cover-map : isConnectedFun k cover-map

hasConnectedCover : (n k : HLevel) (X : Type ℓ) → Type (ℓ-suc ℓ)
hasConnectedCover n k X = ∥ ConnectedCover n k X ∥₁

isPropHasConnectedCover : (n k : HLevel) (X : Type ℓ) → isProp (hasConnectedCover n k X)
isPropHasConnectedCover n k X = PT.isPropPropTrunc

EnoughConnectedCovers : (ℓ : Level) (n k : HLevel) → Type _
EnoughConnectedCovers ℓ n k = (X : Type ℓ) → hasConnectedCover n k X

isPropEnoughConnectedCovers : (n k : HLevel) → isProp (EnoughConnectedCovers ℓ n k)
isPropEnoughConnectedCovers n k = isPropΠ $ isPropHasConnectedCover n k

hasConnectedChoice∞ : (n k : HLevel) (X : Type ℓ) (Y : X → TypeOfHLevel ℓ n) → Type _
hasConnectedChoice∞ n k X Y = ((x : X) → isConnected k ⟨ Y x ⟩) → isConnected k ((x : X) → ⟨ Y x ⟩)

ACC∞ : (ℓ : Level) (n k : HLevel) → Type _
ACC∞ ℓ n k = ∀ (X : Type ℓ) (Y : X → TypeOfHLevel ℓ n) → hasConnectedChoice∞ n k X Y

CFCS∞ : (ℓ : Level) (n k : HLevel) → Type _
CFCS∞ ℓ n k =
  ∀ (X : Type ℓ)
    (Y : TypeOfHLevel ℓ n)
    (f : X → ⟨ Y ⟩)
  → isConnectedFun k f
  ---------------------------
  → isConnectedHasSection k f

isPropCFCS∞ : (n k : HLevel) → isProp (CFCS∞ ℓ n k)
isPropCFCS∞ n k = isPropΠ4 λ X Y f conn → isPropHasConnectedSections k f

CFCS∞→CFCS : ∀ n k → CFCS∞ ℓ n k → CFCS ℓ n k
CFCS∞→CFCS 0 0 cfcs∞ = ConnectedFunsHaveConnectedSections[ 0 ,0]
CFCS∞→CFCS 0 (suc k) cfcs∞ = ConnectedFunsHaveConnectedSections[0,1+ k ]
CFCS∞→CFCS 1 zero cfcs∞ = ACC→ConnectedFunsHaveConnectedSections 1 0 ACC[ 1 ,0]
CFCS∞→CFCS 1 (suc k) cfcs∞ = ACC→ConnectedFunsHaveConnectedSections 1 (suc k) ACC[1,1+ k ]
CFCS∞→CFCS (suc (suc n)) k cfcs∞ = λ { X Y → cfcs∞ ⟨ X ⟩ (⟨ Y ⟩ , isOfHLevelPlus' 2 (str Y)) }

CFCS∞→EnoughConnectedCovers : ∀ n k → CFCS∞ ℓ n k → EnoughConnectedCovers ℓ n k
CFCS∞→EnoughConnectedCovers n k cfcs∞ X = conn-cover where
  tr : X → ∥ X ∥ n
  tr = Tr.∣_∣ₕ

  ∥X∥ₙ : TypeOfHLevel _ n
  ∥X∥ₙ = ∥ X ∥ n , Tr.isOfHLevelTrunc n

  conn-sections-tr : isConnected k (hasSection tr)
  conn-sections-tr = cfcs∞ X ∥X∥ₙ tr {! !}

  conn-cover : hasConnectedCover n k X
  conn-cover = {! !}

CFCS∞≃CFCS×EnoughConnectedCovers : ∀ n k → CFCS∞ ℓ n k ≃ (CFCS ℓ n k × EnoughConnectedCovers ℓ n k)
CFCS∞≃CFCS×EnoughConnectedCovers n k = propBiimpl→Equiv
  (isPropCFCS∞ n k)
  (isProp× (isPropCFCS n k) (isPropEnoughConnectedCovers n k))
  {! !}
  {! !}
