module GpdCont.StrictGroupoid.Properties where

open import GpdCont.StrictGroupoid.Base

open import GpdCont.Prelude
open import GpdCont.HomotopySet
open import GpdCont.SetTruncation using (isSurjection-∣-∣₂ ; isConnected-fiber-∣-∣₂ ; setTruncateFstΣ≃ ; setTruncate⊎≃)
open import GpdCont.Connectivity
open import GpdCont.Axioms.TruncatedChoice using (hasSetChoice ; ASC)
open import GpdCont.Axioms.ConnectedChoice using (ConnectedFunsHaveConnectedSections ; AllSurjectionsSplit→CFCS[2,-])
open import GpdCont.Axioms.Cover using (AllSurjectionsSplitω)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (hasSection ; isEquiv→isContrHasSection)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.PropositionalTruncation.Monad using (_>>=_ ; return)

private
  variable
    ℓ ℓA ℓB : Level
    A B : Type ℓ

CFCS₃₂→mereStrictStr : ConnectedFunsHaveConnectedSections ℓ 3 2 → (A : hGroupoid ℓ) → ∥ StrictGroupoidStr ⟨ A ⟩ ∥₁
CFCS₃₂→mereStrictStr cfcs A*@(A , is-groupoid-A) = PT.map mk mere-section where
  
  mk : hasSection {A = A} ∣_∣₂ → StrictGroupoidStr A
  mk (pt , pt-section) .StrictGroupoidStr.is-groupoid = is-groupoid-A
  mk (pt , pt-section) .StrictGroupoidStr.pt = pt
  mk (pt , pt-section) .StrictGroupoidStr.pt-section = pt-section

  is-connected-hasSection-∣-∣₂ : isConnected 2 (hasSection ∣_∣₂)
  is-connected-hasSection-∣-∣₂ = cfcs A* (∥ A ∥₂ , ST.isSetSetTrunc) ∣_∣₂
    $ isPathConnectedFun→is2ConnectedFun isConnected-fiber-∣-∣₂

  mere-section : ∃[ pt ∈ (∥ A ∥₂ → A) ] section ∣_∣₂ pt
  mere-section = isConnectedSuc→merelyInh 1 is-connected-hasSection-∣-∣₂

ACω→mereStricStr : AllSurjectionsSplitω ℓ → (A : hGroupoid ℓ) → ∥ StrictGroupoidStr ⟨ A ⟩ ∥₁
ACω→mereStricStr split A*@(A , is-groupoid-A) = do
  (pt , pt-section) ← split A ∥A∥₂ ∣_∣₂ (isSurjection-∣-∣₂ A)
  return λ where
    .StrictGroupoidStr.is-groupoid → is-groupoid-A
    .StrictGroupoidStr.pt → pt
    .StrictGroupoidStr.pt-section → pt-section
  where
    ∥A∥₂ : hSet _
    ∥A∥₂ .fst = ∥ A ∥₂
    ∥A∥₂ .snd = ST.isSetSetTrunc

StrictGroupoidStr× :
    StrictGroupoidStr A
  → StrictGroupoidStr B
  → StrictGroupoidStr (A × B)
StrictGroupoidStr× {A} {B} strict-A strict-B = strict-Σ where
  module A = StrictGroupoidStr strict-A
  module B = StrictGroupoidStr strict-B

  is-groupoid-× : isGroupoid (A × B)
  is-groupoid-× = isGroupoid× A.is-groupoid B.is-groupoid

  pt : ∥ A × B ∥₂ → A × B
  pt = ST.rec→Gpd.fun is-groupoid-× pt₀ pt₀-coh where
    pt₀ : A × B → A × B
    pt₀ (a , b) .fst = A.pt-at a
    pt₀ (a , b) .snd = B.pt-at b

    pt₀-coh : ∀ x y → (p q : x ≡ y) → cong pt₀ p ≡ cong pt₀ q
    pt₀-coh (a₀ , b₀) (a₁ , b₁) p q i j .fst = A.pt (ST.squash₂ ∣ a₀ ∣₂ ∣ a₁ ∣₂ (cong (∣_∣₂ ∘ fst) p) (cong (∣_∣₂ ∘ fst) q) i j)
    pt₀-coh (a₀ , b₀) (a₁ , b₁) p q i j .snd = B.pt (ST.squash₂ ∣ b₀ ∣₂ ∣ b₁ ∣₂ (cong (∣_∣₂ ∘ snd) p) (cong (∣_∣₂ ∘ snd) q) i j)

  pt-section : section ∣_∣₂ pt
  pt-section = ST.elim (λ x → ST.isSetPathImplicit) λ where
    (a , b) → ST.PathIdTrunc₀Iso .Iso.inv $ PT.map2 ≡-× (A.mere-retract a) (B.mere-retract b)

  strict-Σ : StrictGroupoidStr _
  strict-Σ .StrictGroupoidStr.is-groupoid = is-groupoid-×
  strict-Σ .StrictGroupoidStr.pt = pt
  strict-Σ .StrictGroupoidStr.pt-section = pt-section

_×ˢ_ : StrictGroupoid ℓA → StrictGroupoid ℓB → StrictGroupoid (ℓ-max ℓA ℓB)
((A , is-strict-A) ×ˢ (B , is-strict-B)) .fst = A × B
((A , is-strict-A) ×ˢ (B , is-strict-B)) .snd = StrictGroupoidStr× is-strict-A is-strict-B

StrictGroupoidStr⊎ :
    StrictGroupoidStr A
  → StrictGroupoidStr B
  → StrictGroupoidStr (A ⊎ B)
StrictGroupoidStr⊎ {A} {B} strict-A strict-B = strict-⊎ where
  module A = StrictGroupoidStr strict-A
  module B = StrictGroupoidStr strict-B

  pt₀ : ∥ A ∥₂ ⊎ ∥ B ∥₂ → A ⊎ B
  pt₀ = Sum.rec (inl ∘ A.pt) (inr ∘ B.pt)

  pt : ∥ A ⊎ B ∥₂ → A ⊎ B
  pt = pt₀ ∘ equivFun setTruncate⊎≃

  pt-section : section ∣_∣₂ pt
  pt-section = mkTruncSection _ mere-retract where
    mere-retract : (x : A ⊎ B) → ∥ pt ∣ x ∣₂ ≡ x ∥₁
    mere-retract (inl a) = PT.map (cong inl) (A.mere-retract a)
    mere-retract (inr b) = PT.map (cong inr) (B.mere-retract b)

  strict-⊎ : StrictGroupoidStr _
  strict-⊎ .StrictGroupoidStr.is-groupoid = Sum.isOfHLevel⊎ 1 A.is-groupoid B.is-groupoid
  strict-⊎ .StrictGroupoidStr.pt = pt
  strict-⊎ .StrictGroupoidStr.pt-section = pt-section

_⊎ˢ_ : ∀ {ℓA ℓB} → StrictGroupoid ℓA → StrictGroupoid ℓB → StrictGroupoid (ℓ-max ℓA ℓB)
((A , is-strict-A) ⊎ˢ (B , is-strict-B)) .fst = A ⊎ B
((A , is-strict-A) ⊎ˢ (B , is-strict-B)) .snd = StrictGroupoidStr⊎ is-strict-A is-strict-B

StrictGroupoidStrΣSet : ∀ {A : Type ℓA} {B : A → Type ℓB}
  → isSet A
  → (∀ a → StrictGroupoidStr (B a))
  → StrictGroupoidStr (Σ A B)
StrictGroupoidStrΣSet {A} {B} is-set-A strict-B = strict-Σ where
  module B a = StrictGroupoidStr (strict-B a)

  is-groupoid-Σ : isGroupoid (Σ A B)
  is-groupoid-Σ = isGroupoidΣ (isSet→isGroupoid is-set-A) B.is-groupoid

  pt-equiv : ∥ Σ A B ∥₂ ≃ Σ A (∥_∥₂ ∘ B)
  pt-equiv = setTruncateFstΣ≃ is-set-A

  pt' : Σ A (∥_∥₂ ∘ B) → Σ A B
  pt' (a , b) .fst = a
  pt' (a , b) .snd = B.pt a b

  pt'-section : section (map-snd ∣_∣₂) pt'
  pt'-section (a , ∣b∣) = ΣPathP (refl′ a , B.pt-section a ∣b∣)

  pt : ∥ Σ A B ∥₂ → Σ A B
  pt = equivFun pt-equiv ⋆ pt'

  pt-section : section ∣_∣₂ pt
  pt-section = mkTruncSection pt (uncurry mere-retract) where
    mere-retract : (a : A) (b : B a) → ∥ Path (Σ A B) (a , B.pt a ∣ b ∣₂) (a , b) ∥₁
    mere-retract a b = do
      pt∣b∣≡b ← B.mere-retract a b
      return $ ΣPathP (refl′ a , pt∣b∣≡b)

  strict-Σ : StrictGroupoidStr _
  strict-Σ .StrictGroupoidStr.is-groupoid = is-groupoid-Σ
  strict-Σ .StrictGroupoidStr.pt = pt
  strict-Σ .StrictGroupoidStr.pt-section = pt-section

StrictGroupoidΣSet : (A : hSet ℓA) (B : ⟨ A ⟩ → StrictGroupoid ℓB) → StrictGroupoid (ℓ-max ℓA ℓB)
StrictGroupoidΣSet A B .fst = Σ[ a ∈ ⟨ A ⟩ ] ⟨ B a ⟩
StrictGroupoidΣSet A B .snd = StrictGroupoidStrΣSet (str A) (str ∘ B)
{-# INJECTIVE_FOR_INFERENCE StrictGroupoidΣSet #-}

{-
StrictGroupoidStrΠ : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB}
  → (∀ a → StrictGroupoidStr (B a))
  → StrictGroupoidStr (∀ a → B a)
StrictGroupoidStrΠ {A} {B} strict-B = strict-Π where
  module B a = StrictGroupoidStr (strict-B a)

  pt : ∥ (∀ a → B a) ∥₂ → (∀ a → B a)
  pt x a = B.pt a $ ST.map (_$ a) x

  pt-section : section ∣_∣₂ pt
  pt-section = ST.elim (λ _ → ST.isSetPathImplicit) λ f → cong ∣_∣₂ (funExt λ a → equivFun (PT.propTruncIdempotent≃ {! !}) (B.mere-retract a (f a))) where

  strict-Π : StrictGroupoidStr _
  strict-Π .StrictGroupoidStr.is-groupoid = isGroupoidΠ B.is-groupoid
  strict-Π .StrictGroupoidStr.pt = pt
  strict-Π .StrictGroupoidStr.pt-section = pt-section

StrictGroupoidStrFun : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB}
  → StrictGroupoidStr A
  → StrictGroupoidStr B
  → StrictGroupoidStr (A → B)
StrictGroupoidStrFun {A} {B} strict-A strict-B = strict-fun where
  module A = StrictGroupoidStr strict-A
  module B = StrictGroupoidStr strict-B

  pt : ∥ (A → B) ∥₂ → A → B
  pt f a = B.pt $ ST.map (_$ a) f

  pt-section : section ∣_∣₂ pt
  pt-section = ST.elim (λ _ → ST.isSetPathImplicit) {! !} where
    lemma : (f : A → B) → ∥ (λ a → B.pt ∣ f a ∣₂) ≡ f ∥₁
    lemma f = do
      return $ funExt λ a → {! !}

  strict-fun : StrictGroupoidStr _
  strict-fun .StrictGroupoidStr.is-groupoid = isGroupoidΠ λ _ → B.is-groupoid
  strict-fun .StrictGroupoidStr.pt = {! !}
  strict-fun .StrictGroupoidStr.pt-section = {! !}
-}

StrictGroupoidStrΣ : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB}
  → StrictGroupoidStr A
  → (∀ a → StrictGroupoidStr (B a))
  → StrictGroupoidStr (Σ A B)
StrictGroupoidStrΣ {A} {B} strict-A strict-B = strict-Σ where
  module A = StrictGroupoidStr strict-A
  module B a = StrictGroupoidStr (strict-B a)

  is-groupoid-Σ : isGroupoid (Σ A B)
  is-groupoid-Σ = isGroupoidΣ A.is-groupoid B.is-groupoid

  pt-fibΣ : ∥ Σ A B ∥₂ → Σ[ x ∈ ∥ Σ A B ∥₂ ] fiber ∣_∣₂ x
  pt-fibΣ = ST.rec→Gpd.fun
    (isGroupoidΣ (isSet→isGroupoid ST.isSetSetTrunc) λ x → isGroupoidΣ is-groupoid-Σ λ a → isSet→isGroupoid ST.isSetPathImplicit)
    impl
    (λ { (a₀ , b₀) (a₁ , b₁) p q → {! !} })
    where
      -- impl' : Σ A B → Σ[ y ∈ ∥ Σ A B ∥₂ ] Σ[ x ∈ Σ A B ] ∣ x ∣₂ ≡ y
      -- impl' (a , b) .fst = ∣ A.pt-at a , {! !} ∣₂
      -- impl' x .snd = {! !}

      impl : Σ A B → Σ[ x ∈ ∥ Σ A B ∥₂ ] fiber ∣_∣₂ x
      impl (a , b) .fst = ∣ a , b ∣₂
      impl (a , b) .snd .fst .fst = a
      impl (a , b) .snd .fst .snd = b
      impl (a , b) .snd .snd = refl

      coh : (a₀ : A) (b₀ : B a₀) (a₁ : A) (b₁ : B a₁) (p q : (a₀ , b₀) ≡ (a₁ , b₁)) → cong impl p ≡ cong impl q
      coh a₀ b₀ a₁ b₁ p q i j .fst = ST.squash₂ {! !} {! !} (cong ∣_∣₂ p) (cong ∣_∣₂ q) i j
      coh a₀ b₀ a₁ b₁ p q i j .snd = {! !}

  pt : ∥ Σ A B ∥₂ → Σ A B
  pt = ST.rec→Gpd.fun is-groupoid-Σ pt₀ pt₀-coh where
    pt₀-fst : A → A
    pt₀-fst a = A.pt-at a

    pt₀-snd : ∀ {a} (b : B a) → ∥ A.pt ∣ a ∣₂ ≡ a ∥₁ → ∥ B (A.pt-at a) ∥₂
    pt₀-snd {a} b = PT.rec→Set ST.isSetSetTrunc b₀ b₀-2-const where
      b₀ : A.pt ∣ a ∣₂ ≡ a → ∥ B (A.pt-at a) ∥₂
      b₀ retr = ∣ subst B (sym retr) b ∣₂

      b₀-2-const : ∀ p q → b₀ p ≡ b₀ q
      b₀-2-const p q = ST.PathIdTrunc₀Iso .Iso.inv {!subst-filler B (sym p) b !}

    pt₀ : Σ A B → Σ A B
    pt₀ (a , b) .fst = pt₀-fst a
    pt₀ (a , b) .snd = B.pt _ (pt₀-snd b (A.mere-retract a))

    pt₀-coh : ∀ x y → (p q : x ≡ y) → cong pt₀ p ≡ cong pt₀ q
    pt₀-coh (a₀ , b₀) (a₁ , b₁) p q i j .fst = A.pt (ST.squash₂ ∣ a₀ ∣₂ ∣ a₁ ∣₂ (cong (∣_∣₂ ∘ fst) p) (cong (∣_∣₂ ∘ fst) q) i j)
    pt₀-coh (a₀ , b₀) (a₁ , b₁) p q i j .snd = {! !}

  strict-Σ : StrictGroupoidStr _
  strict-Σ .StrictGroupoidStr.is-groupoid = is-groupoid-Σ
  strict-Σ .StrictGroupoidStr.pt = pt
  strict-Σ .StrictGroupoidStr.pt-section = {! !}

module _ (is-set-A : isSet A) (strict-B : StrictGroupoidStr B) where
  private
    module B = StrictGroupoidStr strict-B

    PtwiseRetr : (f : A → B) → A → hSet _
    PtwiseRetr f a .fst = B.pt ∣ f a ∣₂ ≡ f a
    PtwiseRetr f a .snd = B.is-groupoid _ _


  StrictGroupoidStrSetFun : ((f : A → B) → hasSetChoice (A , is-set-A) (PtwiseRetr f)) → StrictGroupoidStr (A → B)
  StrictGroupoidStrSetFun choice = strict-fun where
    pt : ∥ (A → B) ∥₂ → (A → B)
    pt = ST.rec→Gpd.fun (isGroupoidΠ λ _ → B.is-groupoid) (B.pt-at ∘_) coh where
      module _ (f g : A → B) (p q : f ≡ g) where
        coh' : cong (∣_∣₂ ∘_) p ≡ cong (∣_∣₂ ∘_) q
        coh' = funExtSquare λ a → ST.isSetSetTrunc _ _ _ _

        coh : cong (B.pt-at ∘_) p ≡ cong (B.pt-at ∘_) q
        coh j i a = B.pt $ coh' j i a

    pt-section : section ∣_∣₂ pt
    pt-section = mkTruncSection _ λ f → do
      let retr* : ∀ a → ∥ B.pt ∣ f a ∣₂ ≡ f a ∥₁
          retr* = B.mere-retract ∘ f
      PT.map funExt $ choice f retr*

    strict-fun : StrictGroupoidStr _
    strict-fun .StrictGroupoidStr.is-groupoid = isGroupoidΠ λ _ → B.is-groupoid
    strict-fun .StrictGroupoidStr.pt = pt
    strict-fun .StrictGroupoidStr.pt-section = pt-section
