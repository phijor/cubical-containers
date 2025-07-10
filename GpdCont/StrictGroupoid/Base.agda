module GpdCont.StrictGroupoid.Base where

open import GpdCont.Prelude
open import GpdCont.HomotopySet
open import GpdCont.SetTruncation using (isConnected-fiber-∣-∣₂ ; setTruncateFstΣ≃ ; setTruncate⊎≃)
open import GpdCont.Connectivity
open import GpdCont.Axioms.TruncatedChoice using (hasSetChoice)

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
    ℓ : Level
    A : Type ℓ

mkTruncSection : (pt : ∥ A ∥₂ → A) → (∀ a → ∥ pt ∣ a ∣₂ ≡ a ∥₁) → section ∣_∣₂ pt
mkTruncSection pt mere-retract = ST.elim (λ _ → ST.isSetPathImplicit) goal where
  goal : ∀ a → ∣ (pt ∣ a ∣₂) ∣₂ ≡ ∣ a ∣₂
  goal a = ST.PathIdTrunc₀Iso .Iso.inv $ mere-retract a

isPropHasSection-∣-∣₂ : (pt : ∥ A ∥₂ → A) → isProp (section ∣_∣₂ pt)
isPropHasSection-∣-∣₂ pt = isPropΠ λ x → ST.isSetSetTrunc ∣ pt x ∣₂ x

record StrictGroupoidStr (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    is-groupoid : isGroupoid A
    pt : ∥ A ∥₂ → A
    pt-section : section ∣_∣₂ pt

  pt-at : A → A
  pt-at a = pt ∣ a ∣₂

  pt-fiber : (x : ∥ A ∥₂) → fiber ∣_∣₂ x
  pt-fiber x .fst = pt x
  pt-fiber x .snd = pt-section x

  mere-retract : ∀ a → ∥ pt ∣ a ∣₂ ≡ a ∥₁
  mere-retract a = ST.PathIdTrunc₀Iso .Iso.fun (pt-section ∣ a ∣₂)

  as-groupoid : hGroupoid ℓ
  as-groupoid .fst = A
  as-groupoid .snd = is-groupoid

  Components : hSet ℓ
  Components .fst = ∥ A ∥₂
  Components .snd = ST.isSetSetTrunc

  isSetTruncFunPt : isOfHLevelFun 2 pt
  isSetTruncFunPt a = isSetΣ ST.isSetSetTrunc λ x → is-groupoid (pt x) a

unquoteDecl StrictGroupoidStrIsoΣ = declareRecordIsoΣ StrictGroupoidStrIsoΣ (quote StrictGroupoidStr)

instance
  StrictGroupoidStrToΣ : RecordToΣ (StrictGroupoidStr A)
  StrictGroupoidStrToΣ = toΣ StrictGroupoidStrIsoΣ

inhFibTrunc→StrictStr : isGroupoid A → ((x : ∥ A ∥₂) → fiber ∣_∣₂ x) → StrictGroupoidStr A
inhFibTrunc→StrictStr is-groupoid-A inh-fib .StrictGroupoidStr.is-groupoid = is-groupoid-A
inhFibTrunc→StrictStr is-groupoid-A inh-fib .StrictGroupoidStr.pt = fst ∘ inh-fib
inhFibTrunc→StrictStr is-groupoid-A inh-fib .StrictGroupoidStr.pt-section = snd ∘ inh-fib

StrictGroupoidStr' : (A : Type ℓ) → Type ℓ
StrictGroupoidStr' A = hasSection {A = A} ∣_∣₂ × isGroupoid A

StrictGroupoidStr'' : (A : Type ℓ) → Type ℓ
StrictGroupoidStr'' A = Σ[ pt ∈ (∥ A ∥₂ → A) ] (∀ a → ∥ pt ∣ a ∣₂ ≡ a ∥₁)

StrictGroupoid : (ℓ : Level) → Type (ℓ-suc ℓ)
StrictGroupoid ℓ = TypeWithStr ℓ StrictGroupoidStr

StrictGroupoid≡ : {G H : StrictGroupoid ℓ}
  → (p : ⟨ G ⟩ ≡ ⟨ H ⟩)
  → (q : PathP (λ i → StrictGroupoidStr (p i)) (str G) (str H))
  → G ≡ H
StrictGroupoid≡ = curry ΣPathP

StrictGroupoid→hGroupoid : StrictGroupoid ℓ → hGroupoid ℓ
StrictGroupoid→hGroupoid (G , is-strict-G) .fst = G
StrictGroupoid→hGroupoid (G , is-strict-G) .snd = StrictGroupoidStr.is-groupoid is-strict-G

is2GroupoidStrictGroupoid : is2Groupoid (StrictGroupoid ℓ)
is2GroupoidStrictGroupoid = isOfHLevelRespectEquiv 4 shuffle is2GroupoidStrictGroupoid' where
  StrictGroupoid' : Type (ℓ-suc ℓ)
  StrictGroupoid' = Σ[ G ∈ hGroupoid _ ] hasSection (∣_∣₂ {A = ⟨ G ⟩})

  to : StrictGroupoid' → StrictGroupoid ℓ
  to ((G , is-groupoid-G) , pt , pt-section) .fst = G
  to ((G , is-groupoid-G) , pt , pt-section) .snd .StrictGroupoidStr.is-groupoid = is-groupoid-G
  to ((G , is-groupoid-G) , pt , pt-section) .snd .StrictGroupoidStr.pt = pt
  to ((G , is-groupoid-G) , pt , pt-section) .snd .StrictGroupoidStr.pt-section = pt-section

  from : StrictGroupoid ℓ → StrictGroupoid'
  from (G , G-str) .fst .fst = G
  from (G , G-str) .fst .snd = StrictGroupoidStr.is-groupoid G-str
  from (G , G-str) .snd .fst = StrictGroupoidStr.pt G-str
  from (G , G-str) .snd .snd = StrictGroupoidStr.pt-section G-str

  shuffle : StrictGroupoid' ≃ StrictGroupoid ℓ
  shuffle = isoToEquiv λ where
    .Iso.fun → to
    .Iso.inv → from
    .Iso.leftInv ((G , is-groupoid-G) , pt , pt-section) i .fst .fst → G
    .Iso.leftInv ((G , is-groupoid-G) , pt , pt-section) i .fst .snd → is-groupoid-G
    .Iso.leftInv ((G , is-groupoid-G) , pt , pt-section) i .snd .fst → pt
    .Iso.leftInv ((G , is-groupoid-G) , pt , pt-section) i .snd .snd → pt-section
    .Iso.rightInv (G , G-str) i .fst → G
    .Iso.rightInv (G , G-str) i .snd .StrictGroupoidStr.is-groupoid → G-str .StrictGroupoidStr.is-groupoid
    .Iso.rightInv (G , G-str) i .snd .StrictGroupoidStr.pt → G-str .StrictGroupoidStr.pt
    .Iso.rightInv (G , G-str) i .snd .StrictGroupoidStr.pt-section → G-str .StrictGroupoidStr.pt-section

  is2GroupoidStrictGroupoid' : is2Groupoid StrictGroupoid'
  is2GroupoidStrictGroupoid' = is2GroupoidΣ (isOfHLevelTypeOfHLevel 3)
    λ G → isOfHLevelSuc 3 (isGroupoidΣ (isGroupoidΠ λ _ → str G)
    λ pt → isProp→isOfHLevelSuc 2 (isPropHasSection-∣-∣₂ pt))

module _ (G : StrictGroupoid ℓ) where
  private module G = StrictGroupoidStr (str G)

  component-pt : (j : ⟨ G.Components ⟩) → fiber ∣_∣₂ j
  component-pt j .fst = G.pt j
  component-pt j .snd = G.pt-section j

  Component≡ : ∀ {j : ⟨ G.Components ⟩} → {x y : fiber ∣_∣₂ j} → x .fst ≡ y .fst → x ≡ y
  Component≡ = Σ≡Prop λ g → ST.isSetSetTrunc ∣ g ∣₂ _

  GroupAtStr : (j : ⟨ G.Components ⟩) → StrictGroupoidStr (fiber ∣_∣₂ j)
  GroupAtStr j .StrictGroupoidStr.is-groupoid = isGroupoidΣ G.is-groupoid (λ g → isProp→isOfHLevelSuc 2 (ST.isSetSetTrunc _ j))
  GroupAtStr j .StrictGroupoidStr.pt = const $ component-pt j
  GroupAtStr j .StrictGroupoidStr.pt-section = mkTruncSection _ mere-retract where
    mere-retract : (x : fiber ∣_∣₂ j) → ∥ component-pt j ≡ x ∥₁
    mere-retract  = isPathConnected→merePath (isConnected-fiber-∣-∣₂ j) (component-pt j)

  GroupAt : ⟨ G.Components ⟩ → StrictGroupoid ℓ
  GroupAt j .fst = fiber ∣_∣₂ j
  GroupAt j .snd = GroupAtStr j

  isHGroupGroupAt : ∀ j → isPathConnected ⟨ GroupAt j ⟩
  isHGroupGroupAt = isConnected-fiber-∣-∣₂

module _ (G : StrictGroupoid ℓ) where
  private module G = StrictGroupoidStr (str G)
  elimProp : ∀ {ℓP} {P : ⟨ G ⟩ → Type ℓP}
    → (∀ g → isProp (P g))
    → (f* : (x : ∥ ⟨ G ⟩ ∥₂) → P (G.pt x))
    → (∀ g → P g)
  elimProp {P} is-prop-P f* g = equivFun (PT.propTruncIdempotent≃ (is-prop-P g)) ∣p∣ where
    p' : P (G.pt-at g)
    p' = f* ST.∣ g ∣₂

    ∣p∣ : ∥ P g ∥₁
    ∣p∣ = do
      q ← G.mere-retract g
      return $ subst P (the (G.pt-at g ≡ g) q) p'

  open import Cubical.Foundations.Interpolate

  {-
  recSetEquiv : ∀ {ℓY} {Y : Type ℓY}
    → isSet Y
    → (f : ⟨ G.Components ⟩ → Y)
    → ⟨ G ⟩ → Y
  recSetEquiv {Y} is-set-Y = {! !} where
    equiv : (x₀ : ⟨ G.Components ⟩) → Y ≃ ((Σ[ g ∈ ⟨ G ⟩ ] ∣ g ∣₂ ≡ x₀) → Y)
    equiv x₀ = isPathConnected→constEquiv (isHGroupGroupAt G x₀) is-set-Y
    
    fun : ⟨ G.Components ⟩ → Y
    fun x₀ = invEq (equiv x₀) λ { (g , p) → {! G.mere-retract !} }

  elimSet : ∀ {ℓX} {X : ⟨ G ⟩ → Type ℓX}
    → (∀ g → isSet (X g))
    → (f* : (g₀ : ∥ ⟨ G ⟩ ∥₂) → X (G.pt g₀))
    → (link* : (g₀ : ∥ ⟨ G ⟩ ∥₂) → (p q : G.pt g₀ ≡ G.pt g₀) → {! !})
      -- PathP (λ i → X (G.pt ?)) (cong (f* ∘ ∣_∣₂) p) {! cong (f* ∘ ∣_∣₂) q !})
    → (∀ g → X g)
  elimSet {X} is-set-X f* link* g = x** where
    foo : G.pt-at g ≡ g → X g
    foo p = subst X p (f* ∣ g ∣₂)

    foo-filler : (p : G.pt ∣ g ∣₂ ≡ g) → PathP (λ i → X (p i)) (f* ∣ g ∣₂) (foo p)
    foo-filler p = subst-filler X p (f* ∣ g ∣₂)

    2-const-foo : (p q : G.pt-at g ≡ g) → foo p ≡ foo q
    2-const-foo p q = {! cong (λ p → subst X p (f* ∣ g ∣₂)) !}
    -- 2-const-foo p q i = comp X* (λ { j (i = i0) → foo-filler p j ; j (i = i1) → foo-filler q j })
    --   (f* {! !}) where
    --   X* : (j : I) → Type _
    --   X* j = {! !}

      -- sys : (j : I) → PartialP (i ∨ ~ i) (X* i j)
      -- sys = {! !}
      -- doubleCompPathP (λ i j → X {!  !}) (foo-filler p) {! !} (foo-filler q)

    x** : X g
    x** = PT.rec→Set (is-set-X g) foo 2-const-foo (G.mere-retract g)
  -}
