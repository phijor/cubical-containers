module GpdCont.StrictGroupoid.Properties where

open import GpdCont.StrictGroupoid.Base
open import GpdCont.StrictGroupoid.HomotopyGroup

open import GpdCont.Prelude
open import GpdCont.Prelude.Square
open import GpdCont.HomotopySet
open import GpdCont.SetTruncation
open import GpdCont.Connectivity
open import GpdCont.Univalence
import      GpdCont.SetTruncation as ST
open import GpdCont.Axioms.TruncatedChoice using (hasSetChoice ; ASC)
open import GpdCont.Axioms.ConnectedChoice using (ConnectedFunsHaveConnectedSections ; AllSurjectionsSplit→CFCS[2,-])
open import GpdCont.Axioms.Cover using (AllSurjectionsSplitω)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (hasSection ; isEquiv→isContrHasSection ; congEquiv)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed using (Pointed)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.PropositionalTruncation.Monad using (_>>=_ ; return)

private
  variable
    ℓ ℓA ℓB : Level
    A B : Type ℓ

CFCS₃₂→mereStrictStr : ConnectedFunsHaveConnectedSections ℓ 3 2
  → (A : hGroupoid ℓ) → ∥ StrictGroupoidStr ⟨ A ⟩ ∥₁
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

CFCS₃₂≃mereStrictStr : ConnectedFunsHaveConnectedSections ℓ 3 2 ≃ ((A : hGroupoid ℓ) → ∥ StrictGroupoidStr ⟨ A ⟩ ∥₁)
CFCS₃₂≃mereStrictStr {ℓ} =
  ConnectedFunsHaveConnectedSections ℓ 3 2 ≃⟨ {! !} ⟩
  ((A : hGroupoid ℓ) → ∥ hasSection ∣_∣₂ ∥₁) ≃⟨ equivΠCod (λ { (A , is-groupoid-A) → propBiimpl→Equiv {! !} {! !} {! !} {! !} } ) ⟩
  ((A : hGroupoid ℓ) → ∥ StrictGroupoidStr ⟨ A ⟩ ∥₁) ≃∎

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

componentEquiv→StrictGroupoidStr : ∀ (A₀ : Type ℓ)
  → isSet A₀
  → isGroupoid A
  → (e : ∥ A ∥₂ ≃ A₀)
  → (pt₀ : A₀ → A)
  → (pt₀-section : section (equivFun e ∘ ∣_∣₂) pt₀)
  → StrictGroupoidStr A
componentEquiv→StrictGroupoidStr {A} A₀ is-set-A₀ is-groupoid-A (e , is-equiv-e) pt₀ pt₀-section = strict-A where
  pt : ∥ A ∥₂ → A
  pt = pt₀ ∘ e

  pt-section : section ∣_∣₂ pt
  pt-section x = invEq (congEquiv (e , is-equiv-e)) p where
    p : e ∣ pt₀ (e x) ∣₂ ≡ e x
    p = pt₀-section (e x)

  strict-A : StrictGroupoidStr A
  strict-A .StrictGroupoidStr.is-groupoid = is-groupoid-A
  strict-A .StrictGroupoidStr.pt = pt
  strict-A .StrictGroupoidStr.pt-section = pt-section

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

-- anti-Σ-snd : ∀ {A : Type ℓA} {B : A → Type ℓB}
--   → StrictGroupoidStr (Σ A B)
--   → StrictGroupoidStr A
--   → (∀ a → isSet (B a))

StrictGroupoidStrΣSnd : ∀ {A : Type ℓA} {B : A → Type ℓB}
  → StrictGroupoidStr A
  → (∀ a → isSet (B a))
  → StrictGroupoidStr (Σ A B)
StrictGroupoidStrΣSnd {A} {B} strict-A is-set-B = strict-Σ where
  module A = StrictGroupoidStr strict-A

  is-groupoid-Σ : isGroupoid (Σ A B)
  is-groupoid-Σ = isGroupoidΣ A.is-groupoid $ isSet→isGroupoid ∘ is-set-B

  inh-fib : ∥ Σ A B ∥₂ → Σ[ x ∈ ∥ Σ A B ∥₂ ] fiber ∣_∣₂ x
  inh-fib = ST.rec→Gpd.fun (isGroupoidΣ (isSet→isGroupoid ST.isSetSetTrunc) λ x → isGroupoidΣ is-groupoid-Σ {! !})
    {! !}
    {! !}
    where
      pt-B : (a : A) → ∥ a ≡ A.pt-at a ∥₁ → (b : B a) → B (A.pt-at a)
      pt-B a = PT.elim→Set (λ _ → isSet→ (is-set-B _)) (subst B) λ p q → funExt λ b → {!subst-filler B p b !}

      fib* : Σ A B → Σ[ x ∈ ∥ Σ A B ∥₂ ] fiber ∣_∣₂ x
      fib* (a , b) .fst = ∣ a , b ∣₂
      fib* (a , b) .snd .fst = A.pt-at a , {! !}
      fib* (a , b) .snd .snd = {! !}

  pt : ∥ Σ A B ∥₂ → Σ A B
  pt = ST.rec→Gpd.fun is-groupoid-Σ pt* {! !} where
    pt* : Σ A B → Σ A B
    pt* (a , b) .fst = A.pt-at a
    pt* (a , b) .snd = {! !}

  pt-section : section ∣_∣₂ pt
  pt-section = {! !}

  strict-Σ : StrictGroupoidStr _
  strict-Σ .StrictGroupoidStr.is-groupoid = is-groupoid-Σ
  strict-Σ .StrictGroupoidStr.pt = pt
  strict-Σ .StrictGroupoidStr.pt-section = pt-section
  
StrictGroupoidStrΣSndHGroup : ∀ {A : Type ℓA} {B : A → Type ℓB}
  → StrictGroupoidStr A
  → (∀ a → StrictGroupoidStr (B a))
  → (∀ a → isPathConnected (B a))
  → StrictGroupoidStr (Σ A B)
StrictGroupoidStrΣSndHGroup {A} {B} strict-A strict-B conn-B = strict-Σ where
  module A = StrictGroupoidStr strict-A
  module B a where
    open StrictGroupoidStr (strict-B a) public

    base : ∥ B a ∥₂
    base = conn-B a .fst

    ptᴰ : B a
    ptᴰ = pt base

  is-groupoid-Σ : isGroupoid (Σ A B)
  is-groupoid-Σ = isGroupoidΣ A.is-groupoid B.is-groupoid

  pt′ : ∥ A ∥₂ → Σ A B
  pt′ x .fst = A.pt x
  pt′ x .snd = B.ptᴰ (A.pt x)

  pt-equiv : ∥ Σ A B ∥₂ ≃ ∥ A ∥₂
  pt-equiv =
    ∥ Σ A B ∥₂ ≃⟨ isoToEquiv ST.setSigmaIso ⟩
    ∥ Σ A (∥_∥₂ ∘ B) ∥₂ ≃⟨ setTruncEquiv (Σ-contractSnd conn-B) ⟩
    ∥ A ∥₂ ≃∎

  strict-Σ : StrictGroupoidStr (Σ A B)
  strict-Σ = componentEquiv→StrictGroupoidStr
    ∥ A ∥₂ ST.isSetSetTrunc
    is-groupoid-Σ
    pt-equiv
    pt′ A.pt-section

_⋉ˢ_ : ∀ {ℓA ℓB} → (A : StrictGroupoid ℓA) → (B : ⟨ A ⟩ → hGroup ℓB) → StrictGroupoid (ℓ-max ℓA ℓB)
((A , strict-A) ⋉ˢ B) .fst = Σ[ a ∈ A ] ⟨ B a .fst ⟩
((A , strict-A) ⋉ˢ B) .snd = StrictGroupoidStrΣSndHGroup strict-A (str ∘ fst ∘ B) (snd ∘ B)

-- Semidirect product of groups:
isHGroup-⋉ˢ : ∀ {ℓA ℓB}
  → (A : StrictGroupoid ℓA)
  → (B : ⟨ A ⟩ → hGroup ℓB)
  → isHGroup A
  → isHGroup (A ⋉ˢ B)
isHGroup-⋉ˢ A B is-group-A = isPathConnectedΣ is-group-A (snd ∘ B)

-- XXX: This does work if B has at least one component
_⋉*_ : ∀ {ℓA ℓB} → (A : StrictGroupoid ℓA) → (B : ⟨ A ⟩ → StrictGroupoid ℓB) → StrictGroupoid (ℓ-max ℓA ℓB)
A ⋉* B = A ⋉ˢ B' where module _ (a : ⟨ A ⟩) where
  open StrictGroupoidStr (str (B a))

  B∙ : Pointed _
  B∙ .fst = ⟨ B a ⟩
  B∙ .snd = pt {! !}

  B' : hGroup _
  B' = {! Aut∙ B∙ is-groupoid !}

Autˢ : (A : hGroupoid ℓA) (pt : ∥ ⟨ A ⟩ ∥₂ → ⟨ A ⟩) → StrictGroupoid ℓA
Autˢ A pt .fst = Σ[ a ∈ ⟨ A ⟩ ] ∥ pt ∣ a ∣₂ ≡ a ∥₁
Autˢ A pt .snd = inhFibTrunc→StrictStr
  (isGroupoidΣ (str A) (λ a → isProp→isOfHLevelSuc 2 PT.isPropPropTrunc))
  (ST.elim→Gpd {! !} f {! !})
  where
    Aᶜ = Σ[ a ∈ ⟨ A ⟩ ] ∥ pt ∣ a ∣₂ ≡ a ∥₁

    f : (y : Aᶜ) → Σ[ x ∈ Aᶜ ] ∣ x ∣₂ ≡ ∣ y ∣₂
    f (a , h) .fst = a , h
    f (a , h) .snd = refl

    wd : (x y : Aᶜ) (p q : x ≡ y) → SquareP (λ i j → fiber ∣_∣₂ (squash-cong p q i j)) (cong f p) (cong f q) refl refl
    wd (a₀ , h₀) (a₁ , h₁) p q = ΣSquarePSet ? (ΣSquarePProp (λ _ → PT.isPropPropTrunc) {! !})
-- Autˢ A pt .snd .StrictGroupoidStr.is-groupoid = 
-- Autˢ A pt .snd .StrictGroupoidStr.pt = λ { x → {! !} }
-- Autˢ A pt .snd .StrictGroupoidStr.pt-section = {! !}

_⋉ᴬ_ : ∀ {ℓA ℓB} → (A : StrictGroupoid ℓA) → (B : ⟨ A ⟩ → StrictGroupoid ℓB) → StrictGroupoid (ℓ-max ℓA ℓB)
A ⋉ᴬ B = {! Aut !}

-- _⋉_ : ∀ {ℓA ℓB} → (A : hGroup ℓA) → (B : ⟨ A .fst ⟩ → hGroup ℓB) → hGroup _
-- ((A , _) ⋉ B) .fst = A ⋉ˢ B
-- ((A , is-group-A) ⋉ B) .snd = isHGroup-⋉ˢ A B is-group-A

module _ {ℓG ℓH ℓX}
  (G : StrictGroupoid ℓG)
  (X : ⟨ G ⟩ → hSet ℓX)
  where
  private module G = StrictGroupoidStr (str G)

  module _ (H : ∀ g → ⟨ X g ⟩ → hGroup ℓH) where

    private
      module H g x = StrictGroupoidStr (str (H g x .fst))

      is-conn-H : ∀ g (x : ⟨ X g ⟩) → isPathConnected ⟨ H g x .fst ⟩
      is-conn-H g x = H g x .snd

      X[_]→H : ⟨ G ⟩ → hGroupoid _
      X[_]→H g .fst = (x : ⟨ X g ⟩) → ⟨ H g x .fst ⟩
      X[_]→H g .snd = isGroupoidΠ (H.is-groupoid g)

      f₀ : ∀ g → ⟨ X[ g ]→H ⟩
      f₀ g x = H.pt g x (is-conn-H g x .fst)

      ΠH : ⟨ G ⟩ → hGroup _
      ΠH g = {! Aut X[ g ]→H (f₀ g) !}

    Wrˢ : StrictGroupoid _
    Wrˢ = G ⋉ˢ ΠH

    isHGroup-Wrˢ : isHGroup G → isHGroup Wrˢ
    isHGroup-Wrˢ = isHGroup-⋉ˢ G ΠH

-- Wr : ∀ {ℓG ℓH ℓX}
--   → (G : hGroup ℓG)
--   → (X : ⟨ G .fst ⟩ → hSet ℓX)
--   → (H : ∀ g → ⟨ X g ⟩ → hGroup ℓH)
--   → hGroup _
-- Wr G X H .fst = Wrˢ (G .fst) X H
-- Wr G X H .snd = isHGroup-Wrˢ (G .fst) X H (G .snd)

module Test {ℓG ℓH ℓX}
  (G : StrictGroupoid ℓG)
  (X : ⟨ G ⟩ → hSet ℓX)
  (H : ∀ g → ⟨ X g ⟩ → hGroup ℓH)
  where

  module FinSet where
    open import Cubical.Data.FinSet public
    open import Cubical.Data.FinSet.FiniteChoice public

  open FinSet using (isFinSet ; FinSet)

  module H where
    [_,_] : (g : ⟨ G ⟩) (x : ⟨ X g ⟩) → Type _
    [_,_] = λ g x → ⟨ H g x .fst ⟩

    pt : (g : ⟨ G ⟩) (x : ⟨ X g ⟩)
      → ∥ [ g , x ] ∥₂
      → [ g , x ]
    pt g x = StrictGroupoidStr.pt $ str (H g x .fst)

    is-connected : (g : ⟨ G ⟩) (x : ⟨ X g ⟩) → isPathConnected [ g , x ]
    is-connected g x = H g x .snd

    pt-at : (g : ⟨ G ⟩) (x : ⟨ X g ⟩) → [ g , x ]
    pt-at g x = pt g x (is-connected g x .fst)

  test : ⟨ Wrˢ G X H ⟩ ≡ (Σ[ g ∈ ⟨ G ⟩ ] Σ[ f ∈ ((x : ⟨ X g ⟩) → H.[ g , x ]) ] (∣ f ∣₂ ≡ ∣ H.pt-at g ∣₂))
  test = refl

  isFiniteAction : (∀ g → isFinSet ⟨ X g ⟩) → ⟨ Wrˢ G X H ⟩ ≃ (Σ[ g ∈ ⟨ G ⟩ ] (∀ x → H.[ g , x ]))
  isFiniteAction is-finset-X = Σ-cong-equiv-snd $ Σ-contractSnd ∘ is-contr-pres-strict where
    Xᶠ : ⟨ G ⟩ → FinSet ℓX
    Xᶠ g .fst = ⟨ X g ⟩
    Xᶠ g .snd = is-finset-X g

    module _ (g : ⟨ G ⟩) (f : ∀ x → H.[ g , x ]) where
      mere-htpy : ∀ x → ∥ f x ≡ H.pt-at g x ∥₁
      mere-htpy x = isPathConnected→merePath (H.is-connected g x) (f x) (H.pt-at g x)

      lemma : ∣ f ∣₂ ≡ ∣ H.pt-at g ∣₂
      lemma = merePath→pathSetTrunc do
        htpy ← FinSet.choice (Xᶠ g) (λ x → f x ≡ H.pt-at g x) mere-htpy
        return $ funExt htpy

      is-contr-pres-strict : isContr (∣ f ∣₂ ≡ ∣ H.pt-at g ∣₂)
      is-contr-pres-strict = inhProp→isContr lemma (ST.isSetSetTrunc _ _)

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

isStrictΣ : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB}
  → ∥ StrictGroupoidStr A ∥₁
  → (∀ a → ∥ StrictGroupoidStr (B a) ∥₁)
  → ∥ StrictGroupoidStr (Σ A B) ∥₁
isStrictΣ {A} {B} is-strict-A is-strict-B = do
  inh-fib ← isSurjection-∣-∣₂ (Σ A B) {! !}
  return $ inhFibTrunc→StrictStr is-groupoid-Σ {! !}
  where

  is-groupoid-Σ : isGroupoid (Σ A B)
  is-groupoid-Σ = equivFun (PT.propTruncIdempotent≃ isPropIsGroupoid) $ do
    strict-A ← is-strict-A
    let is-groupoid-A = strict-A .StrictGroupoidStr.is-groupoid
    return $ isGroupoidΣ is-groupoid-A λ a → equivFun (PT.propTruncIdempotent≃ isPropIsGroupoid) $
      PT.map StrictGroupoidStr.is-groupoid (is-strict-B a)

  fib : ∥ ((x : ∥ Σ A B ∥₂) → fiber ∣_∣₂ x) ∥₁
  fib = {! !}

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
