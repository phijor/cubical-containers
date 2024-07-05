module GpdCont.QuotientContainer.Examples where

open import GpdCont.Prelude
open import GpdCont.QuotientContainer.Base
open import GpdCont.QuotientContainer.Premorphism
open import GpdCont.QuotientContainer.Morphism
open import GpdCont.QuotientContainer.Category

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.Extend using (extend₂)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (substIso)
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.Foundations.Equiv.Properties using (equivAdjointEquiv)
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary.Base
open import Cubical.Data.Unit
open import Cubical.Data.Bool as Bool hiding (_⊕_)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using () renaming (rec to ex-falso)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms using (GroupIso)
open import Cubical.Algebra.Group.MorphismProperties using (GroupIso→GroupEquiv)
open import Cubical.Algebra.Group.GroupPath using (GroupPath)
open import Cubical.Categories.Category using (isUnivalent ; CatIso ; isPropIsIso ; pathToIso)

open QCont hiding (_⁻¹ ; _·_)
open Premorphism
open Morphism

UPair : QCont ℓ-zero
UPair .Shape = Unit
UPair .Pos _ = Bool
UPair .isSymm σ = Unit
UPair .is-set-shape = isSetUnit
UPair .is-set-pos _ = isSetBool
UPair .is-prop-symm _ = isPropUnit
UPair .symm-id _ = tt
UPair .symm-sym _ _ = tt
UPair .symm-comp _ _ _ _ = tt

Id×UPair : QCont ℓ-zero
Id×UPair .Shape = Unit
Id×UPair .Pos _ = Unit ⊎ Bool
Id×UPair .isSymm σ = equivFun σ (inl tt) ≡ inl tt
Id×UPair .is-set-shape = isSetUnit
Id×UPair .is-set-pos _ = isSet⊎ isSetUnit isSetBool
Id×UPair .is-prop-symm _ = isSet⊎ isSetUnit isSetBool _ _
Id×UPair .symm-id _ = refl
Id×UPair .symm-sym σ σ-fix-0 = sym (invEq (equivAdjointEquiv σ) σ-fix-0)
Id×UPair .symm-comp σ τ σ-fix-0 τ-fix-0 = cong (equivFun τ) σ-fix-0 ∙ τ-fix-0

private
  open module UPair = QCont UPair using (_⁻¹) renaming (_·_ to _⊕_)
  module ℤ₂ = GroupStr (UPair.SymmGroupStr tt)

  ℤ₂ : Type _
  ℤ₂ = UPair.Symm tt

  swap : ℤ₂
  swap .fst = notEquiv
  swap .snd = tt

  data Graph (f : Bool → Bool) : Type where
    inspect : (x y : Bool)
      → f true ≡ x
      → f false ≡ y
      → Graph f

  graph : (f : Bool → Bool) → Graph f
  graph f = inspect (f true) (f false) refl refl

  open import Cubical.Algebra.AbGroup using (AbGroup ; IsAbGroup ; AbGroupPath)
  open import Cubical.Algebra.Group.Instances.Bool using (BoolGroup ; ≅Bool)

  module BoolGroup = GroupStr (str BoolGroup)

  isCommBoolGroup : ∀ (x y : ⟨ BoolGroup ⟩) → x BoolGroup.· y ≡ y BoolGroup.· x
  isCommBoolGroup false false = refl
  isCommBoolGroup false true = refl
  isCommBoolGroup true false = refl
  isCommBoolGroup true true = refl

  BoolAb : AbGroup ℓ-zero
  BoolAb .fst = Bool
  BoolAb .snd = {! !}

  opaque
    SymmIso : GroupIso BoolGroup (UPair.SymmGroup tt)
    SymmIso = ≅Bool $ invIso $ compIso BoolReflection.reflectIso (compIso univalenceIso $ equivToIso $ invEquiv (Σ-contractSnd λ _ → isContrUnit))

    BoolGroup≡SymmGroup : BoolGroup ≡ (UPair.SymmGroup tt)
    BoolGroup≡SymmGroup = equivFun (GroupPath BoolGroup (UPair.SymmGroup tt)) (GroupIso→GroupEquiv SymmIso)

  SymmAb : AbGroup ℓ-zero
  SymmAb = {!AbGroupPath _ BoolAb !}

isCommUPairSymm : ∀ (g h : ℤ₂) → g ⊕ h ≡ h ⊕ g
isCommUPairSymm = {!(IsAbGroup.+Comm) !} where

swap₀-pos : Premorphism UPair UPair $ id (UPair .Shape)
swap₀-pos .Premorphism.pos-mor _ = id _
swap₀-pos .Premorphism.symm-pres _ = id _
swap₀-pos .Premorphism.symm-pres-natural _ _ = refl

swap₀ : Morphism UPair UPair
swap₀ .Morphism.shape-mor = id (UPair .Shape)
swap₀ .Morphism.pos-equiv = SQ.[ swap₀-pos ]

swap₁-pos : Premorphism UPair UPair $ id (UPair .Shape)
swap₁-pos .Premorphism.pos-mor _ = not
swap₁-pos .Premorphism.symm-pres _ = id _
swap₁-pos .Premorphism.symm-pres-natural tt σ = cong UPair._⁺ $ isCommUPairSymm swap σ

swap₁ : Morphism UPair UPair
swap₁ .Morphism.shape-mor = id (UPair .Shape)
swap₁ .Morphism.pos-equiv = SQ.[ swap₁-pos ]

r : PremorphismEquiv swap₀-pos swap₁-pos
r .PremorphismEquiv.η _ = (notEquiv , tt)
r .PremorphismEquiv.η-comm _ = funExt $ sym ∘ notnot

swap₀≡swap₁ : swap₀ ≡ swap₁
swap₀≡swap₁ i .Morphism.shape-mor = refl i
swap₀≡swap₁ i .Morphism.pos-equiv = pre-morphism-eq/ r i

isEquivPosMorUPairEndomorphism : (f : Premorphism UPair UPair (const tt)) → isEquiv (f .pos-mor tt)
isEquivPosMorUPairEndomorphism f = isoToIsEquiv $ the-iso (f .pos-mor tt) (f .symm-pres tt) (f .symm-pres-natural tt) where
  module _ (f : Bool → Bool) (φ : ℤ₂ → ℤ₂) (nat : ∀ (g : ℤ₂) → f UPair.▷ g ≡ φ g UPair.◁ f) where
    ¬f-const : (c : Bool) → ¬ (∀ b → f b ≡ c)
    ¬f-const c f-const = not≢const c contra where
      contra : not c ≡ c
      contra =
        not c ≡⟨ cong not $ sym (f-const c) ⟩
        not (f c) ≡⟨ funExt⁻ (nat swap) c ⟩
        f ((φ swap UPair.⁺) c) ≡⟨ f-const _ ⟩
        c ∎

    is-iso : Σ[ inv ∈ (Bool → Bool) ] (section f inv) × (retract f inv)
    is-iso with (graph f)
    ... | inspect true false p q = id _ , Bool.elim p q , Bool.elim p q
    ... | inspect false true p q = not , Bool.elim q p , Bool.elim (cong not p) (cong not q)
    ... | inspect false false f-true≡false f-false≡false = ex-falso $ ¬f-const false f-const where
      f-const : ∀ b → f b ≡ false
      f-const = Bool.elim f-true≡false f-false≡false
    ... | inspect true true f-true≡true f-false≡true = ex-falso $ ¬f-const true f-const where
      f-const : ∀ b → f b ≡ true
      f-const = Bool.elim f-true≡true f-false≡true

    the-iso : Iso Bool Bool
    the-iso .Iso.fun = f
    the-iso .Iso.inv = is-iso .fst
    the-iso .Iso.rightInv = is-iso .snd .fst
    the-iso .Iso.leftInv = is-iso .snd .snd

UPairEndomorphism→Symm : Premorphism UPair UPair (const tt) → ℤ₂
UPairEndomorphism→Symm f .fst = _ , isEquivPosMorUPairEndomorphism f
UPairEndomorphism→Symm f .snd = tt

isPropUPairEndomorphism : isProp (Morphism UPair UPair)
isPropUPairEndomorphism = MorphismElimProp2 _≡_ isSetMorphism goal where
  open Premorphism
  open PremorphismEquiv

  _≈?_ : (f g : Premorphism UPair UPair (const tt)) → PremorphismEquiv f g
  (f ≈? g) = f≈?g where
    fˢ gˢ : ℤ₂
    fˢ = UPairEndomorphism→Symm f
    gˢ = UPairEndomorphism→Symm g

    f≈?g : PremorphismEquiv f g
    f≈?g .η tt = fˢ ⊕ gˢ ⁻¹
    f≈?g .η-comm tt =
      (fˢ UPair.⁺) ≡⟨ cong UPair._⁺ (ℤ₂.·IdR fˢ) ⟩
      (fˢ ⊕ ℤ₂.1g) UPair.⁺ ≡⟨ cong (λ · → (fˢ ⊕ ·) UPair.⁺) $ sym (ℤ₂.·InvL gˢ) ⟩
      (fˢ ⊕ (gˢ ⁻¹ ⊕ gˢ)) UPair.⁺ ≡⟨⟩
      (fˢ ⊕ gˢ ⁻¹) UPair.◁ (gˢ UPair.⁺) ∎

  goal' : (f g : Premorphism UPair UPair (const tt)) → pre→mor f ≡ pre→mor g
  goal' f g i .shape-mor = const tt
  goal' f g i .pos-equiv = pre-morphism-eq/ (f ≈? g) i

  goal : (u v : Unit → Unit) → (f : Premorphism UPair UPair u) → (g : Premorphism UPair UPair v) → pre→mor f ≡ pre→mor g
  goal u v = goal'

isContrUPairEndomorphism : isContr (Morphism UPair UPair)
isContrUPairEndomorphism = inhProp→isContr swap₀ isPropUPairEndomorphism

UPairPath : UPair ≡ UPair
UPairPath i .Shape = Unit
UPairPath i .Pos _ = notEq i
UPairPath i .isSymm _ = Unit
UPairPath i .is-set-shape = isSetUnit
UPairPath i .is-set-pos _ = isProp→PathP (λ i → isPropIsSet {A = notEq i}) isSetBool isSetBool i
UPairPath i .is-prop-symm _ _ _ _ = tt
UPairPath i .symm-id _ = tt
UPairPath i .symm-sym _ _ = tt
UPairPath i .symm-comp _ _ _ _ = tt

¬UPairPath≡refl : ¬ UPairPath ≡ refl
¬UPairPath≡refl upair-path-compare = false≢true false≡true where
  bool-path-compare : notEq ≡ refl
  bool-path-compare i j = upair-path-compare i j .Pos (isSet→SquareP {A = λ i j → upair-path-compare i j .Shape} (λ i j → upair-path-compare i j .is-set-shape) refl refl refl refl i j)

  false≡true : false ≡ true
  false≡true i = transport (bool-path-compare i) true

¬isSetQCont : ¬ isSet (QCont ℓ-zero)
¬isSetQCont is-set-qcont = ¬UPairPath≡refl $ is-set-qcont _ _ UPairPath refl

¬isUnivalentQCONT : ¬ isUnivalent (QCONT ℓ-zero)
¬isUnivalentQCONT univ = ¬UPairPath≡refl UPairPath≡refl where
  isPropUPairAutomorphism : isProp (CatIso (QCONT _) UPair UPair)
  isPropUPairAutomorphism = isPropΣ isPropUPairEndomorphism isPropIsIso

  compare : pathToIso UPairPath ≡ pathToIso refl
  compare = isPropUPairAutomorphism _ _

  UPairPath≡refl : UPairPath ≡ refl
  UPairPath≡refl = isoFunInjective (equivToIso $ _ , isUnivalent.univ univ _ _) UPairPath refl compare
