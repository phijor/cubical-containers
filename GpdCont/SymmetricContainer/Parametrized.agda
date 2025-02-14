{-# OPTIONS --lossy-unification #-}
module GpdCont.SymmetricContainer.Parametrized where

open import GpdCont.SymmetricContainer.Base

open import GpdCont.Prelude
open import GpdCont.Equiv using (lineEquiv)
open import GpdCont.Univalence
open import GpdCont.HLevels
open import GpdCont.HomotopySet
open import GpdCont.SymmetricContainer.TwoCategory hiding (module ⟦-⟧)
open import GpdCont.Polynomial
open import GpdCont.W
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.StrictFunctor
open import GpdCont.TwoCategory.HomotopyGroupoid using (hGpdCat)
open import GpdCont.TwoCategory.GroupoidEndo using (Endo)
open import GpdCont.TwoCategory.TwoDiscrete
open import GpdCont.TwoCategory.Algebra
open import GpdCont.TwoCategory.Initial



open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (compIso to _∙ᵢ_)
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Involution using (isInvolution)
open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty using (⊥ ; ⊥*)
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor using () renaming (_$_ to _$ꟳ_)

record ContainerP {ℓ : Level} (Ix : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    Shape : hGroupoid ℓ
    Pos : Ix → ⟨ Shape ⟩ → hSet ℓ

private
  variable
    ℓ : Level
    Ix : Type ℓ

⟦_⟧ : {Ix : Type ℓ} → ContainerP Ix → (Ix → hGroupoid ℓ) → hGroupoid ℓ
⟦_⟧ {Ix} F X = Σʰ[ 3 ∣ s ∈ F.Shape ] Πʰ[ 3 ∣ ix ∈ Ix ] (⟨ F.Pos ix s ⟩ →₃ X ix) where
  module F = ContainerP F

ContainerP⁺¹ : (Ix : Type ℓ) → Type (ℓ-suc ℓ)
ContainerP⁺¹ Ix = ContainerP (Maybe Ix)

pattern free = nothing
pattern param ix = just ix

record MorphismP {Ix : Type ℓ} (F G : ContainerP Ix) : Type ℓ where
  private
    module F = ContainerP F
    module G = ContainerP G
  field
    shape-map : ⟨ F.Shape ⟩ → ⟨ G.Shape ⟩
    pos-map : ∀ ix s → ⟨ G.Pos ix (shape-map s) ⟩ → ⟨ F.Pos ix s ⟩

unquoteDecl MorphismPIsoΣ = declareRecordIsoΣ MorphismPIsoΣ (quote MorphismP)

instance
  MorphismPToΣ : ∀ {F G : ContainerP Ix} → RecordToΣ (MorphismP F G)
  MorphismPToΣ {F} {G} = toΣ (MorphismPIsoΣ {F = F} {G = G})

module _ {Ix : Type ℓ} {F G : ContainerP Ix} {f g : MorphismP F G} where
  private
    module F = ContainerP F
    module G = ContainerP G
  open MorphismP

  MorphismP≡ : (p : f .shape-map ≡ g .shape-map)
    → (q : PathP (λ i → ∀ ix s → ⟨ G.Pos ix (p i s) ⟩ → ⟨ F.Pos ix s ⟩) (f .pos-map) (g .pos-map))
    → f ≡ g
  MorphismP≡ p q i .shape-map = p i
  MorphismP≡ p q i .pos-map = q i

  MorphismP≡Ext :
    ((s : ⟨ F.Shape ⟩) → Σ[ p ∈ f .shape-map s ≡ g .shape-map s ] ((ix : Ix) → PathP (λ i → ⟨ G.Pos ix (p i) ⟩ → ⟨ F.Pos ix s ⟩) (f .pos-map ix s) (g .pos-map ix s)))
    → f ≡ g
  MorphismP≡Ext pq i .shape-map s = pq s .fst i
  MorphismP≡Ext pq i .pos-map ix s = pq s .snd ix i

module _ {Ix : Type ℓ} {F G : ContainerP Ix} where
  private
    module F = ContainerP F
    module G = ContainerP G
  open MorphismP

  MorphismPSquare :
    ∀ {f₀₀ f₀₁ f₁₀ f₁₁ : MorphismP F G}
    → {p₀₋ : f₀₀ ≡ f₀₁} {p₁₋ : f₁₀ ≡ f₁₁}
    → {p₋₀ : f₀₀ ≡ f₁₀} {p₋₁ : f₀₁ ≡ f₁₁}
    → (shape-sq : Square (cong shape-map p₀₋) (cong shape-map p₁₋) (cong shape-map p₋₀) (cong shape-map p₋₁))
    → (pos-sq : SquareP (λ i j → ∀ ix s → ⟨ G.Pos ix (shape-sq i j s) ⟩ → ⟨ F.Pos ix s ⟩) (cong pos-map p₀₋) (cong pos-map p₁₋) (cong pos-map p₋₀) (cong pos-map p₋₁))
    → Square p₀₋ p₁₋ p₋₀ p₋₁
  MorphismPSquare shape-sq pos-sq i j .shape-map = shape-sq i j
  MorphismPSquare shape-sq pos-sq i j .pos-map = pos-sq i j

isGroupoidMorphismP : (F G : ContainerP Ix) → isGroupoid (MorphismP F G)
isGroupoidMorphismP F G = recordIsOfHLevel 3 $
  isGroupoidΣ (isGroupoidΠ λ _ → str G.Shape) λ where
    shape-map → isGroupoidΠ3 λ ix s _ → isSet→isGroupoid (str (F.Pos ix s))
  where
    module F = ContainerP F
    module G = ContainerP G

idP : (F : ContainerP Ix) → MorphismP F F
idP F .MorphismP.shape-map = id _
idP F .MorphismP.pos-map ix s = id _

compP : {F G H : ContainerP Ix} → (φ : MorphismP F G) → (γ : MorphismP G H) → MorphismP F H
compP φ γ = compP-def where
  module φ = MorphismP φ
  module γ = MorphismP γ

  compP-def : MorphismP _ _
  compP-def .MorphismP.shape-map = φ.shape-map ⋆ γ.shape-map
  compP-def .MorphismP.pos-map ix s = γ.pos-map ix _ ⋆ φ.pos-map ix s

module _ (Ix : Type ℓ) where
  ContainerPᵂ : WildCat (ℓ-suc ℓ) ℓ
  ContainerPᵂ .WildCat.ob = ContainerP Ix
  ContainerPᵂ .WildCat.Hom[_,_] = MorphismP
  ContainerPᵂ .WildCat.id = idP _
  ContainerPᵂ .WildCat._⋆_ = compP
  ContainerPᵂ .WildCat.⋆IdL φ = refl
  ContainerPᵂ .WildCat.⋆IdR φ = refl
  ContainerPᵂ .WildCat.⋆Assoc φ γ η = refl

  ContainerPCat : TwoCategory (ℓ-suc ℓ) ℓ ℓ
  ContainerPCat = TwoDiscrete ContainerPᵂ isGroupoidMorphismP

Container : (ℓ : Level) → Type (ℓ-suc ℓ)
Container ℓ = ContainerP Unit*

Container1 : (ℓ : Level) → Type (ℓ-suc ℓ)
Container1 ℓ = ContainerP⁺¹ ⊥*

Container2 : (ℓ : Level) → Type (ℓ-suc ℓ)
Container2 ℓ = ContainerP⁺¹ Unit*

Container→SymmetricContainer : Container ℓ → SymmetricContainer ℓ
Container→SymmetricContainer F = mkSymmetricContainer Shape (Pos _) where
  open ContainerP F

⟦_⟧₁ : Container ℓ → (hGroupoid ℓ → hGroupoid ℓ)
⟦_⟧₁ F X = ⟦ F ⟧ (const X)

{-

module BinTree where
  private
    module Endo = TwoCategory (Endo ℓ-zero)
    module ⟦-⟧ = StrictFunctor (⟦-⟧ {ℓ-zero})

  data BranchShape : Type where
    leaf branch : BranchShape

  isGroupoidBranchShape : isGroupoid BranchShape
  isGroupoidBranchShape = isGroupoidRetract
    (λ { leaf → true ; branch → false })
    (λ { true → leaf ; false → branch })
    (λ { leaf → refl ; branch → refl })
    (isSet→isGroupoid isSetBool)

  data BranchPos : Type where
    left right : BranchPos

  BranchFree : BranchShape → hSet _
  BranchFree leaf = ⊥ , λ ()
  BranchFree branch .fst = BranchPos
  BranchFree branch .snd = isSetRetract
    (λ { left → true ; right → false })
    (λ { false → right ; true → left })
    (λ { left → refl ; right → refl })
    isSetBool

  BranchParam : BranchShape → hSet _
  BranchParam leaf = Unit , isSetUnit
  BranchParam branch = ⊥ , λ ()

  -- B(X, Y) = X + (Y × Y)
  Branch : Container2 ℓ-zero
  Branch .ContainerP.Shape = BranchShape , isGroupoidBranchShape
  Branch .ContainerP.Pos x@(param _) = BranchParam
  Branch .ContainerP.Pos y@free = BranchFree

  -- BinTree = Leaf X | Branch BinTree BinTree
  BinTree : Container ℓ-zero
  BinTree = Mu.μ Branch

  module μBranch = Mu Branch

  ⟦BinTree⟧ : Endo.ob
  ⟦BinTree⟧ = ⟦-⟧.₀ (Container→SymmetricContainer BinTree)

  data BT (X : Type) : Type where
    leaf : (x : X) → BT X
    branch : (left right : BT X) → BT X

  module _ {X : Type} where
    μ→BT'-branch :
      ∀ (sub-shape : BranchPos → W BranchShape (⟨_⟩ ∘ BranchFree))
      → (⟨ μBranch.μ-pos _ (sup-W branch sub-shape) ⟩ → X)
      → (pos : BranchPos)
      → Σ[ s ∈ W BranchShape (⟨_⟩ ∘ BranchFree) ] (⟨ μBranch.μ-pos _ s ⟩ → X)
    μ→BT'-branch sub-shape label pos .fst = sub-shape pos
    μ→BT'-branch sub-shape label pos .snd = label ∘ there pos

    μ→BT' : (t : W BranchShape (⟨_⟩ ∘ BranchFree)) → (⟨ μBranch.μ-pos _ t ⟩ → X) → BT X
    μ→BT' (sup-W leaf _) = λ label → leaf (label (here tt))
    μ→BT' (sup-W branch sub-shape) = λ label → branch
      (μ→BT' (sub-shape left) (label ∘ there left))
      (μ→BT' (sub-shape right) (label ∘ there right))

    BT→μ : (BT X) → (Σ[ t ∈ W BranchShape (⟨_⟩ ∘ BranchFree) ] (⟨ μBranch.μ-pos _ t ⟩ → X))
    BT→μ (leaf x) .fst = sup-W leaf (λ ())
    BT→μ (leaf x) .snd = λ { (here _) → x }
    BT→μ (branch l r) = μ-branch where
      l' : Σ _ _
      l' = BT→μ l

      r' : Σ _ _
      r' = BT→μ r

      pos : BranchPos → W BranchShape (⟨_⟩ ∘ BranchFree)
      pos left = l' .fst
      pos right = r' .fst

      label : (q : BranchPos) → ⟨ μBranch.μ-pos _ (pos q) ⟩ → X
      label left = l' .snd
      label right = r' .snd

      μ-branch : Σ _ _
      μ-branch .fst = sup-W branch pos
      μ-branch .snd (there q x) = label q x

    μ→BT : (Σ[ t ∈ W BranchShape (⟨_⟩ ∘ BranchFree) ] (⟨ μBranch.μ-pos _ t ⟩ → X)) → (BT X)
    μ→BT = uncurry μ→BT'

    μ-BT-section : section μ→BT BT→μ
    μ-BT-section (leaf x) = refl
    μ-BT-section (branch l r) i = branch (μ-BT-section l i) (μ-BT-section r i)

    {-# TERMINATING #-}
    μ-BT-retract : retract μ→BT BT→μ
    μ-BT-retract (sup-W leaf s , label) i .fst = sup-W leaf (isProp⊥→ (λ ()) s i)
    μ-BT-retract (sup-W leaf s , label) i .snd (here tt) = label (here tt)
    μ-BT-retract (sup-W branch s , label) = goal
      where
        branch-path : ∀ pos → BT→μ (μ→BT (s pos , label ∘ there pos)) ≡ (s pos , label ∘ there pos)
        branch-path pos = μ-BT-retract (s pos , label ∘ there pos)

        goal : BT→μ (μ→BT (sup-W branch s , label)) ≡ (sup-W branch s , label)
        goal = ΣPathP
          ( cong (sup-W branch)
            (λ { i left → branch-path left i .fst
                ; i right → branch-path right i .fst })
            , λ { i (there left x) → branch-path left i .snd x
                ; i (there right x) → branch-path right i .snd x }
            )

    compute-iso : Iso
      (Σ[ t ∈ W BranchShape (⟨_⟩ ∘ BranchFree) ] (Fixᴰ _ _ _ (⟨_⟩ ∘ BranchParam) t → X))
      (BT X)
    compute-iso .Iso.fun = μ→BT
    compute-iso .Iso.inv = BT→μ
    compute-iso .Iso.rightInv = μ-BT-section
    compute-iso .Iso.leftInv = μ-BT-retract

  compute : ∀ X → ⟨ ⟦BinTree⟧ $ꟳ X ⟩ ≃ BT ⟨ X ⟩
  compute (X , is-gpd-X) =
    Polynomial _ _ X ≃⟨ _ ≃Σ ⟩
    Σ[ t ∈ W BranchShape (⟨_⟩ ∘ BranchFree) ] (⟨ μBranch.μ-pos _ t ⟩ → X) ≃⟨ isoToEquiv compute-iso ⟩
    BT X ≃∎

module Mobile where
  data MobileShape : Type where
    leaf : MobileShape
    branch : MobileShape
    swap : branch ≡ branch
    invol : compSquareFiller swap swap refl
    isGroupoidShape : isGroupoid MobileShape

  mobileElim : ∀ {ℓ} {B : MobileShape → Type ℓ}
    → (∀ x → isGroupoid (B x))
    → (leaf* : B leaf)
    → (branch* : B branch)
    → (swap* : PathP (λ i → B (swap i)) branch* branch*)
    → (invol* : compSquarePFiller {B = B} invol swap* swap* refl)
    → (x : MobileShape) → B x
  mobileElim {B} is-gpd-B leaf* branch* swap* invol* = go where
    go : (x : MobileShape) → B x
    go leaf = leaf*
    go branch = branch*
    go (swap i) = swap* i
    go (invol i j) = invol* i j
    go (isGroupoidShape x y p q r s i j k) =
      is-gpd-B'
        (go x) (go y)
        (cong go p) (cong go q)
        (cong (cong go) r) (cong (cong go) s)
        (isGroupoidShape x y p q r s)
        i j k
      where
        is-gpd-B' : isOfHLevelDep 3 B
        is-gpd-B' {a0} {a1} = isOfHLevel→isOfHLevelDep 3 is-gpd-B {a0} {a1}

  mobileElimSet : ∀ {ℓ} {B : MobileShape → Type ℓ}
    → (∀ x → isSet (B x))
    → (leaf* : B leaf)
    → (branch* : B branch)
    → (swap* : PathP (λ i → B (swap i)) branch* branch*)
    → (x : MobileShape) → B x
  mobileElimSet {B} is-set-B leaf* branch* swap* = mobileElim (isSet→isGroupoid ∘ is-set-B) leaf* branch* swap* invol* where
    invol* : compSquarePFiller {B = B} invol swap* swap* refl
    invol* = isSet→SquareP (λ i j → is-set-B (invol i j)) _ _ _ _

  mobileRec : ∀ {ℓ} {A : Type ℓ}
    → isGroupoid A
    → (leaf* branch* : A)
    → (swap* : Path A branch* branch*)
    → (invol* : compSquareFiller swap* swap* refl)
    → MobileShape → A
  mobileRec is-gpd-A leaf* branch* swap* invol* = go where
    go : MobileShape → _
    go leaf = leaf*
    go branch = branch*
    go (swap i) = swap* i
    go (invol i j) = invol* i j
    go (isGroupoidShape x y p q r s i j k) =
      is-gpd-A
        (go x) (go y)
        (cong go p) (cong go q)
        (cong (cong go) r) (cong (cong go) s)
        i j k

  SideSet : hSet ℓ-zero
  SideSet .fst = Bool
  SideSet .snd = isSetBool

  pattern left = true
  pattern right = false

  left≢right : ¬ left ≡ right
  left≢right = true≢false

  right≢left : ¬ right ≡ left
  right≢left = false≢true

  swapEquiv : ⟨ SideSet ⟩ ≃ ⟨ SideSet ⟩
  swapEquiv = notEquiv

  mobileHSet : ∀ {ℓ}
    → (Leaf Branch : hSet ℓ)
    → (swap≃ : ⟨ Branch ⟩ ≃ ⟨ Branch ⟩)
    → (invol≃ : PathP (λ i → ⟨ Branch ⟩ ≡ ua swap≃ i) (ua swap≃) refl)
    → MobileShape → hSet ℓ
  mobileHSet Leaf Branch swap≃ invol≃ = mobileRec isGroupoidHSet Leaf Branch (hSet≡ (ua swap≃)) (ΣSquareSet (λ _ → isProp→isSet isPropIsSet) invol≃)

  MobilePos : MobileShape → hSet ℓ-zero
  MobilePos = mobileHSet (EmptySet _) SideSet swapEquiv (subst (PathP (λ j → ⟨ SideSet ⟩ ≡ ua swapEquiv j) (ua swapEquiv)) invol' coh) where
    invol' : ua (swapEquiv ∙ₑ swapEquiv) ≡ refl
    invol' = cong ua (equivEq (funExt notnot)) ∙ uaIdEquiv

    coh : PathP (λ j → ⟨ SideSet ⟩ ≡ ua swapEquiv j) (ua swapEquiv) (ua (swapEquiv ∙ₑ swapEquiv))
    coh = uaCompEquivSquare swapEquiv swapEquiv

    invol* : PathP (λ i → ⟨ SideSet ⟩ ≡ ua swapEquiv i) (ua swapEquiv) refl
    invol* i j = Glue ⟨ SideSet ⟩ {φ = φ} system where
      φ = ∂² i j

      system : Partial φ (Σ[ T ∈ Type ] T ≃ ⟨ SideSet ⟩)
      system (i = i0) = {!ua-system swapEquiv j !}
      system (i = i1) = {! !}
      system (j = i0) = {! !}
      system (j = i1) = {! !}
      -- system (i = i0) = ua swapEquiv j , {! ua-unglue-equiv′ swapEquiv j !}
      -- system (i = i1) = ⟨ SideSet ⟩ , lineEquiv (λ φ x → x) (idIsEquiv _) (equivIsEquiv (ua-unglue-equiv′ swapEquiv i1)) j
      -- system (j = i0) = ⟨ SideSet ⟩ , idEquiv _
      -- system (j = i1) = ua swapEquiv i , ua-unglue-equiv′ swapEquiv i

  MobilePos-swap : cong (λ p → ⟨ MobilePos p ⟩) swap ≡ ua swapEquiv
  MobilePos-swap = refl

  Mobile : Container1 ℓ-zero
  Mobile .ContainerP.Shape .fst = MobileShape
  Mobile .ContainerP.Shape .snd = isGroupoidShape
  Mobile .ContainerP.Pos free = MobilePos

  TreeC : ContainerP ⊥*
  TreeC = Mu.μ Mobile

  Tree : Type
  Tree = ⟨ TreeC .ContainerP.Shape ⟩

  isGroupoidTree : isGroupoid Tree
  isGroupoidTree = str $ TreeC .ContainerP.Shape

  module Tree where
    leafW : Tree
    leafW = sup-W leaf λ ()

    branchW : (l r : Tree) → Tree
    branchW l r = sup-W branch λ { right → r ; left → l }

    swapW : (l r : Tree) → branchW l r ≡ branchW r l
    -- swapW l r i = sup-W (swap i) λ { p → {! ua-unglue swapEquiv i p  !} }
    swapW l r = cong₂ sup-W swap $ funExtNonDep $ λ where
      {x₀ = right} {x₁ = right} p → Empty.rec $ left≢right (ua-ungluePath swapEquiv p)
      {x₀ = left}  {x₁ = right} p → refl′ l
      {x₀ = right} {x₁ = left}  p → refl′ r
      {x₀ = left}  {x₁ = left}  p → Empty.rec (right≢left (ua-ungluePath swapEquiv p))

  data TreeI : Type where
    leaf : TreeI
    branch : (l r : TreeI) → TreeI
    swap : ∀ l r → branch l r ≡ branch r l
    invol : ∀ l r → PathP (λ i → branch l r ≡ swap r l i) (swap l r) refl
    isGroupoidTreeI : isGroupoid TreeI

  recTreeI : ∀ {ℓ} {B : Type ℓ}
    → isGroupoid B
    → (leaf* : B)
    → (branch* : (l r : B) → B)
    → (swap* : ∀ l r → branch* l r ≡ branch* r l)
    → (invol* : ∀ l r → PathP (λ i → branch* l r ≡ swap* r l i) (swap* l r) refl)
    → TreeI → B
  recTreeI {B} is-gpd-B leaf* branch* swap* invol* = go where
    go : TreeI → B
    go leaf = leaf*
    go (branch l r) = branch* (go l) (go r)
    go (swap l r i) = swap* (go l) (go r) i
    go (invol l r i j) = invol* (go l) (go r) i j
    go (isGroupoidTreeI x y p q r s i j k) = is-gpd-B
      (go x) (go y)
      (cong go p) (cong go q)
      (cong (cong go) r) (cong (cong go) s)
      i j k

  elimTreeI : ∀ {ℓ} {B : TreeI → Type ℓ}
    → (∀ x → isGroupoid (B x))
    → (leaf* : B leaf)
    → (branch* : ∀ {l r} → B l → B r → B (branch l r))
    → (swap* : ∀ {l r} (l* : B l) (r* : B r) → PathP (λ i → B (swap l r i)) (branch* l* r*) (branch* r* l*))
    → (invol* : ∀ {l r} (l* : B l) (r* : B r) → SquareP (λ i j → B (invol l r i j)) (swap* l* r*) refl refl (swap* r* l*))
    → (x : TreeI) → B x
  elimTreeI {B} is-gpd-B leaf* branch* swap* invol* = go where
    is-gpd-dep-B : isOfHLevelDep 3 B
    is-gpd-dep-B {a0} {a1} = isOfHLevel→isOfHLevelDep 3 is-gpd-B {a0} {a1}

    go : (x : TreeI) → B x
    go leaf = leaf*
    go (branch l r) = branch* (go l) (go r)
    go (swap l r i) = swap* (go l) (go r) i
    go (invol l r i j) = invol* (go l) (go r) i j
    go (isGroupoidTreeI x y p q r s i j k) =
      is-gpd-dep-B
        (go x) (go y)
        (cong go p) (cong go q)
        (cong (cong go) r) (cong (cong go) s)
        (isGroupoidTreeI x y p q r s)
        i j k

  elimSetTreeI : ∀ {ℓ} {B : TreeI → Type ℓ}
    → (∀ x → isSet (B x))
    → (leaf* : B leaf)
    → (branch* : ∀ {l r} → B l → B r → B (branch l r))
    → (swap* : ∀ {l r} (l* : B l) (r* : B r) → PathP (λ i → B (swap l r i)) (branch* l* r*) (branch* r* l*))
    → (x : TreeI) → B x
  elimSetTreeI {B} is-set-B leaf* branch* swap* = elimTreeI {B = B} (isSet→isGroupoid ∘ is-set-B) leaf* branch* swap* invol* where
    invol* : ∀ {l r} (l* : B l) (r* : B r) → SquareP (λ i j → B (invol l r i j)) (swap* l* r*) refl refl (swap* r* l*)
    invol* l* r* = isSet→SquareP (λ i j → is-set-B (invol _ _ i j)) _ _ _ _

  swapPathP : ∀ side → PathP (λ i → ua swapEquiv i) side (not side)
  swapPathP side i = ua-gluePt swapEquiv i side

  Tree→TreeI : Tree → TreeI
  Tree→TreeI = WRec (mobileElim (λ x → isGroupoidΠ λ _ → isGroupoidTreeI) leaf* branch* swap* invol*) where
    leaf* : (⊥* → TreeI) → TreeI
    leaf* = const leaf

    branch* : (Bool → TreeI) → TreeI
    branch* sub = branch (sub left) (sub right)

    swap* : PathP (λ i → (ua notEquiv i → TreeI) → TreeI) branch* branch*
    swap* i sub = swap (sub (swapPathP left i)) (sub (swapPathP right i)) i

    invol* : SquareP (λ i j → (⟨ MobilePos (invol i j) ⟩ → TreeI) → TreeI) swap* refl refl swap*
    invol* i j sub = invol (sub (left* i j)) {! !} i j where
      left* : SquareP (λ i j → ⟨ MobilePos (invol i j) ⟩) (swapPathP left) (refl′ left) (refl′ left) (swapPathP right)
      left* i j = {! ⟨ MobilePos (invol i j) ⟩!}

  TreeI→Tree : TreeI → Tree
  TreeI→Tree = recTreeI isGroupoidTree Tree.leafW Tree.branchW Tree.swapW {! !}

  tree-iso : Iso Tree TreeI
  tree-iso .Iso.fun = Tree→TreeI
  tree-iso .Iso.inv = TreeI→Tree
  tree-iso .Iso.rightInv = elimSetTreeI (λ x → isGroupoidTreeI _ _) refl (λ pl pr i → branch (pl i) (pr i)) (λ {l} {r} pl pr i j → swap {! !} {! !} {! !})
  tree-iso .Iso.leftInv = WIndExplicit $ mobileElimSet
    (λ x → isSetΠ2 λ _ _ → isGroupoidTree _ _)
    (λ no-pos _ → cong (sup-W leaf) (isProp⊥*→ _ no-pos))
    (λ _ sub-path → cong (sup-W branch) (funExt λ { right → sub-path right ; left → sub-path left }))
    λ { i t x j → sup-W (swap i) λ { x₁ → {! !} } }
-}
