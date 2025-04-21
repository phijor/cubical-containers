open import GpdCont.Prelude

module GpdCont.StrictGroupoid.Category (ℓ : Level) where

open import GpdCont.StrictGroupoid.Base renaming (StrictGroupoid to StrictGroupoid₀)
open import GpdCont.StrictGroupoid.Morphism
open import GpdCont.StrictGroupoid.Equiv

open import GpdCont.Connectivity
open import GpdCont.SetTruncation
open import GpdCont.HomotopySet
open import GpdCont.Univalence
open import GpdCont.PropositionalTruncation using (propTruncFstΣ≃)
open import GpdCont.Equiv using (equivΠDomain)

open import Cubical.Foundations.Equiv
import      Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Fibration using (totalEquiv ; fiberEquiv)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Groups
open import Cubical.Categories.NaturalTransformation.Base as NT using (_≅ᶜ_)
open import Cubical.Categories.Equivalence.AdjointEquivalence
open import Cubical.Categories.Equivalence.Base using (_≃ᶜ_ ; isEquivalence ; WeakInverse)
open import Cubical.Categories.Equivalence.Properties using (isFullyFaithful+isEquivF-ob→isEquiv)
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import GpdCont.Categories.Family hiding (module Coproducts)
import GpdCont.Categories.Coproducts as Coproducts

open StrictFun

StrictGroupoid : Category (ℓ-suc ℓ) ℓ
StrictGroupoid .Category.ob = StrictGroupoid₀ ℓ
StrictGroupoid .Category.Hom[_,_] = StrictFun
StrictGroupoid .Category.id {x = G} = idStrict G
StrictGroupoid .Category._⋆_ {x = G} {y = H} {z = K} = compStrict G H K
StrictGroupoid .Category.⋆IdL {x = G} {y = H} ψ = StrictFun≡' G H refl λ g → sym (GL.rUnit (strict-fun-str G H ψ ≡$ ∣ g ∣₂))
StrictGroupoid .Category.⋆IdR {x = G} {y = H} φ = StrictFun≡' G H refl λ g → sym (GL.lUnit (strict-fun-str G H φ ≡$ ∣ g ∣₂))
StrictGroupoid .Category.⋆Assoc {x = G} {y = H} {z = K} {w = L} φ ψ ρ = StrictFun≡' G L refl λ g → {! !} -- {! GL.assoc (ρ .snd ≡$ ∣ ψ .fst (φ .fst g) ∣₂) ? ?!}
  -- sym $ the ((_ ∙ _) ∙ _ ≡ _ ∙ (_ ∙ _)) {!GL.assoc ? ? ? !}
StrictGroupoid .Category.isSetHom {x = G} {y = H} = isSetStrictFun G H

private module StrictGroupoid = Category StrictGroupoid

isUnivalentStrictGroupoidCat : isUnivalent StrictGroupoid
isUnivalentStrictGroupoidCat = {! !}

isGroupoidStrictGroupoid : isGroupoid StrictGroupoid.ob
isGroupoidStrictGroupoid = isUnivalent.isGroupoid-ob isUnivalentStrictGroupoidCat

isHGroup : StrictGroupoid.ob → Type _
isHGroup G = isPathConnected ⟨ G ⟩

isPropIsHGroup : ∀ G → isProp (isHGroup G)
isPropIsHGroup G = isPropIsPathConnected ⟨ G ⟩

hGroup : Category (ℓ-suc ℓ) ℓ
hGroup = FullSubcategory StrictGroupoid isHGroup

private
  module hGroup = Category hGroup

opaque
  isUnivalentHGroup : isUnivalent hGroup
  isUnivalentHGroup = isUnivalentFullSub StrictGroupoid isPropIsHGroup isUnivalentStrictGroupoidCat

  isGroupoidHGroup : isGroupoid hGroup.ob
  isGroupoidHGroup = isUnivalent.isGroupoid-ob isUnivalentHGroup

hGroup≡ : ∀ {G H : hGroup.ob} → G .fst ≡ H .fst → G ≡ H
hGroup≡ = Σ≡Prop isPropIsHGroup

ForgetGroup : Functor hGroup StrictGroupoid
ForgetGroup = FullInclusion StrictGroupoid isHGroup
{-# INJECTIVE_FOR_INFERENCE ForgetGroup #-}

module _ where
  open Coproducts StrictGroupoid ℓ using (Coproducts ; Coproduct ; Δ ; UniversalElement)

  StrictGroupoidCoproducts : Coproducts
  StrictGroupoidCoproducts J G = goal where
    open import Cubical.Categories.Adjoint.UniversalElements using (RightAdjointAt')
    ΣG : StrictGroupoid.ob
    ΣG = StrictGroupoidΣSet J G

    module G j = StrictGroupoidStr (str (G j))
    module ΣG = StrictGroupoidStr (str ΣG)

    ι : ∀ j → StrictFun (G j) ΣG
    ι j .fst g .fst = j
    ι j .fst g .snd = g
    ι j .snd = funExt (ST.elim (λ x → ΣG.is-groupoid _ _) λ g → refl)

    universal-equiv : (H : StrictGroupoid.ob) → StrictFun ΣG H ≃ (∀ j → StrictFun (G j) H)
    universal-equiv H =
      StrictFun ΣG H ≃⟨⟩
      Σ[ φ ∈ (⟨ ΣG ⟩ → ⟨ H ⟩) ] StrictFunStr ΣG H φ ≃⟨ Σ-cong-equiv-snd str-equiv ⟩
      Σ[ φ ∈ (⟨ ΣG ⟩ → ⟨ H ⟩) ] ((j : ⟨ J ⟩) (x : ∥ ⟨ G j ⟩ ∥₂) → H.pt (ST.map φ (trunc-snd j x)) ≡ φ (ΣG.pt (trunc-snd j x))) ≃⟨ Σ-cong-equiv-fst curryEquiv ⟩
      Σ[ φ ∈ (∀ j → ⟨ G j ⟩ → ⟨ H ⟩) ] ((j : ⟨ J ⟩) (x : ∥ ⟨ G j ⟩ ∥₂) → H.pt (ST.map (uncurry φ) (trunc-snd j x)) ≡ (uncurry φ) (ΣG.pt (trunc-snd j x)))
        ≃⟨ Σ-cong-equiv-snd (λ φ → equivΠCod λ j → equivΠCod $ path-equiv φ j) ⟩
      Σ[ φ ∈ (∀ j → ⟨ G j ⟩ → ⟨ H ⟩) ] ((j : ⟨ J ⟩) (x : ∥ ⟨ G j ⟩ ∥₂) → H.pt (ST.map (φ j) x) ≡ φ j (G.pt j x)) ≃⟨ invEquiv Σ-Π-≃ ⟩
      (∀ j → Σ[ φ ∈ (⟨ G j ⟩ → ⟨ H ⟩) ] (∀ x → H.pt (ST.map φ x) ≡ φ (G.pt j x))) ≃⟨ equivΠCod (λ j → Σ-cong-equiv-snd $ λ φ → funExtEquiv) ⟩
      (∀ j → StrictFun (G j) H) ≃∎
      where
        module H = StrictGroupoidStr (str H)

        trunc-equiv : ∥ ⟨ ΣG ⟩ ∥₂ ≃ (Σ[ j ∈ ⟨ J ⟩ ] ∥ ⟨ G j ⟩ ∥₂)
        trunc-equiv = setTruncateFstΣ≃ (str J)

        trunc-snd : ∀ j → ∥ ⟨ G j ⟩ ∥₂ → ∥ ⟨ ΣG ⟩ ∥₂
        trunc-snd j x = invEq trunc-equiv (j , x)
        
        module _ (φ : ∀ j → ⟨ G j ⟩ → ⟨ H ⟩) (j : ⟨ J ⟩) where
          path-equiv : (x : ∥ ⟨ G j ⟩ ∥₂) →
            (H.pt (ST.map (uncurry φ) (trunc-snd j x)) ≡ uncurry φ (ΣG.pt (trunc-snd j x)))
              ≃
            (H.pt (ST.map (φ j) x) ≡ φ j (G.pt j x))
          path-equiv = ST.elim
            (λ x → isOfHLevel≃ 2 (H.is-groupoid _ _) (H.is-groupoid _ _))
            (λ g → idEquiv (H.pt ∣ φ j g ∣₂ ≡ φ j (G.pt j ∣ g ∣₂)))

        str-equiv : ∀ φ → StrictFunStr ΣG H φ ≃ ((j : ⟨ J ⟩) (x : ∥ ⟨ G j ⟩ ∥₂) → H.pt (ST.map φ (trunc-snd j x)) ≡ φ (ΣG.pt (trunc-snd j x)))
        str-equiv φ =
          StrictFunStr ΣG H φ ≃⟨ invEquiv funExtEquiv ⟩
          ((x : ∥ ⟨ ΣG ⟩ ∥₂) → H.pt (ST.map φ x) ≡ φ (ΣG.pt x)) ≃⟨ equivΠDomain (invEquiv trunc-equiv) ⟩
          (((j , x) : Σ[ j ∈ ⟨ J ⟩ ] ∥ ⟨ G j ⟩ ∥₂) → H.pt (ST.map φ (trunc-snd j x)) ≡ φ (ΣG.pt (trunc-snd j x))) ≃⟨ curryEquiv ⟩
          ((j : ⟨ J ⟩) (x : ∥ ⟨ G j ⟩ ∥₂) → H.pt (ST.map φ (trunc-snd j x)) ≡ φ (ΣG.pt (trunc-snd j x))) ≃∎
      
    module _ (H : StrictGroupoid.ob) where
      univ-map : StrictFun ΣG H → ∀ j → StrictFun (G j) H
      univ-map f j = compStrict (G j) ΣG H (ι j) f
      {-# INJECTIVE_FOR_INFERENCE univ-map #-}

      opaque
        is-universal : isEquiv univ-map
        is-universal = subst isEquiv eq $ equivIsEquiv (universal-equiv H) where
          eq : equivFun (universal-equiv H) ≡ univ-map
          eq = funExt₂ λ f j → StrictFun≡' (G j) H refl (lemma f j) where
            lemma : ∀ (f : StrictFun ΣG H) → ∀ j (g : ⟨ G j ⟩) → (f .snd ≡$ ∣ j , g ∣₂) ≡ (f .snd ≡$ ∣ j , g ∣₂) ∙ refl
            lemma f j g = GL.rUnit (f .snd ≡$ ∣ j , g ∣₂)
      
    goal : Coproduct J G
    goal .UniversalElement.vertex = ΣG
    goal .UniversalElement.element = ι
    goal .UniversalElement.universal = is-universal

private
  Fam[hGroup] : Category (ℓ-suc ℓ) ℓ
  Fam[hGroup] = Fam ℓ hGroup

  module Fam[hGroup] = Category Fam[hGroup]

Σˢ : Functor Fam[hGroup] StrictGroupoid
Σˢ = Elim.elimFunctor ℓ hGroup StrictGroupoid StrictGroupoidCoproducts ForgetGroup

private
  module Σˢ = Functor Σˢ renaming (F-ob to ₀ ; F-hom to ₁ ; F-id to id ; F-seq to seq)

private
  module _ (G : StrictGroupoid.ob) where
    private module G = StrictGroupoidStr (str G)
    D₀ᴰ : ⟨ G.Components ⟩ → hGroup.ob
    D₀ᴰ j .fst = GroupAt G j
    D₀ᴰ j .snd = isHGroupGroupAt G j

    D₀ : Fam[hGroup].ob
    D₀ .fst = G.Components
    D₀ .snd = D₀ᴰ

  D₁ : (G H : StrictGroupoid.ob) → StrictGroupoid [ G , H ] → Fam[hGroup] [ D₀ G , D₀ H ]
  D₁ G H (φ , φ-is-strict) = u , f where
    module G = StrictGroupoidStr (str G)
    module H = StrictGroupoidStr (str H)

    u : ⟨ G.Components ⟩ → ⟨ H.Components ⟩
    u = ST.map φ

    module _ (j : ⟨ G.Components ⟩) where
      fˢ : ⟨ GroupAt G j ⟩ → ⟨ GroupAt H (u j) ⟩
      fˢ (g , ∣g∣≡j) .fst = φ g
      fˢ (g , ∣g∣≡j) .snd = the (∣ φ g ∣₂ ≡ ST.map φ j) $ cong (ST.map φ) ∣g∣≡j

      f : hGroup.Hom[ D₀ᴰ G j , D₀ᴰ H (u j) ]
      f .fst = fˢ
      f .snd = funExt λ _ → Component≡ H (φ-is-strict ≡$ j)

  opaque
    D-id : (G : StrictGroupoid.ob) → D₁ G G (idStrict G) ≡ Fam[hGroup].id
    D-id G = FamHom≡ _ _ setTruncMapId $ ST.elim (λ x → isOfHLevelPathP 2 (isSetStrictFun (GroupAt G x) (GroupAt G x)) _ _)
      λ g → StrictFun≡ (GroupAt G _) (GroupAt G _)
        ( funExt (λ _ → Component≡ G refl)
        , funExtSquare {! !}
        )


D : Functor StrictGroupoid Fam[hGroup]
D .Functor.F-ob = D₀
D .Functor.F-hom {x = G} {y = H} = D₁ G H
D .Functor.F-id {x = G} = D-id G
D .Functor.F-seq = {! !}

{-
private
  η₀ : (x : Fam[hGroup].ob) → x ≡ D₀ (Σˢ ⟅ x ⟆)
  η₀ x@(J , G*) = sym $ ΣPathP (hSet≡ (ua components-equiv) , component-at-path) where
    G = fst ∘ G*
    is-connected-G = snd ∘ G*

    components-equiv : ∥ Σ[ j ∈ ⟨ J ⟩ ] ⟨ G j ⟩ ∥₂ ≃ ⟨ J ⟩
    components-equiv =
      ∥ Σ[ j ∈ ⟨ J ⟩ ] ⟨ G j ⟩ ∥₂ ≃⟨ setTruncateFstΣ≃ (str J) ⟩
      Σ[ j ∈ ⟨ J ⟩ ] ∥ ⟨ G j ⟩ ∥₂ ≃⟨ Σ-contractSnd is-connected-G ⟩
      ⟨ J ⟩ ≃∎
    module _ (j : ⟨ J ⟩) (g : ⟨ G j ⟩) where
      equivᴰ : (j′ : ⟨ J ⟩) (g′ : ⟨ G j′ ⟩) → _ ≃ _
      equivᴰ j′ g′ =
        Path (∥ Σ[ j ∈ ⟨ J ⟩ ] ⟨ G j ⟩ ∥₂) ∣ j′ , g′ ∣₂ ∣ j , g ∣₂ ≃⟨ PathSetTrunc≃PropTruncPath ⟩
        ∥ (j′ , g′) ≡ (j , g) ∥₁ ≃⟨ PT.propTrunc≃ $ invEquiv ΣPathP≃PathPΣ ⟩
        ∥ Σ[ p ∈ j′ ≡ j ] PathP (λ i → ⟨ G (p i) ⟩) g′ g ∥₁ ≃⟨ {! !} ⟩
        Σ[ p ∈ j′ ≡ j ] ∥ PathP (λ i → ⟨ G (p i) ⟩) g′ g ∥₁ ≃∎

      equiv : fiber ∣_∣₂ ∣ j , g ∣₂ ≃ ⟨ G j ⟩
      equiv =
        (Σ[ x ∈ Σ[ j ∈ ⟨ J ⟩ ] ⟨ G j ⟩ ] ∣ x ∣₂ ≡ ∣ j , g ∣₂) ≃⟨ Σ-assoc-≃ ⟩
        (Σ[ j′ ∈ ⟨ J ⟩ ] Σ[ g′ ∈ ⟨ G j′ ⟩ ] ∣ j′ , g′ ∣₂ ≡ ∣ j , g ∣₂) ≃⟨ Σ-cong-equiv-snd (λ j′ → Σ-cong-equiv-snd (equivᴰ j′)) ⟩
        (Σ[ j′ ∈ ⟨ J ⟩ ] Σ[ g′ ∈ ⟨ G j′ ⟩ ] Σ[ p ∈ j′ ≡ j ] ∥ PathP (λ i → ⟨ G (p i) ⟩) g′ g ∥₁) ≃⟨ {! !} ⟩
        (Σ[ (j′ , p) ∈ singl j ] Σ[ g′ ∈ ⟨ G j′ ⟩ ] ∥ PathP (λ i → ⟨ G (p (~ i)) ⟩) g′ g ∥₁) ≃⟨ Σ-contractFst (isContrSingl j) ⟩
        (Σ[ g′ ∈ ⟨ G j ⟩ ] ∥ g′ ≡ g ∥₁) ≃⟨ Σ-cong-equiv-snd (λ g′ → invEquiv PathSetTrunc≃PropTruncPath) ⟩
        (Σ[ g′ ∈ ⟨ G j ⟩ ] ∣ g′ ∣₂ ≡ ∣ g ∣₂) ≃⟨ Σ-contractSnd (λ g′ → isContr→isContrPath (is-connected-G j) _ _) ⟩
        ⟨ G j ⟩ ≃∎

    component-at-path : PathP (λ i → ua components-equiv i → hGroup.ob) (D₀ᴰ (Σˢ ⟅ J , G* ⟆)) G*
    component-at-path = ua→ $ ST.elim (λ x → isGroupoidHGroup _ _) {! !}

inv-Σˢ : WeakInverse Σˢ
inv-Σˢ .WeakInverse.invFunc = D
inv-Σˢ .WeakInverse.η = NT.pathToNatIso (Functor≡ η₀ {! !})
inv-Σˢ .WeakInverse.ε = {! !}
-}

isGroupoid-fiber-Σˢ₀ : (H : StrictGroupoid.ob) → isGroupoid (fiber Σˢ.₀ H)
isGroupoid-fiber-Σˢ₀ H = isGroupoidΣ is-groupoid-Fam[hGroup]₀ is-groupoid-StrictGroupoid where
  is-groupoid-Fam[hGroup]₀ : isGroupoid Fam[hGroup].ob
  is-groupoid-Fam[hGroup]₀ = isGroupoidΣ isGroupoidHSet λ J → isGroupoidΠ λ j → isGroupoidHGroup

  is-groupoid-StrictGroupoid : (x : Fam[hGroup].ob) → isGroupoid (Σˢ.₀ x ≡ H)
  is-groupoid-StrictGroupoid x = is2GroupoidStrictGroupoid (Σˢ.₀ x) H

isConnected-fiber-Σˢ₀ : (H : StrictGroupoid.ob) → isConnected 3 (fiber Σˢ.₀ H)
isConnected-fiber-Σˢ₀ H = {! isConnectedΣ !} where
  lemma₁ : isConnected 3 Fam[hGroup].ob
  lemma₁ = {! !}

{-
Σˢ₀-equiv : Fam[hGroup].ob ≃ StrictGroupoid.ob
Σˢ₀-equiv =
  (Σ[ J ∈ hSet ℓ ] (⟨ J ⟩ → hGroup.ob)) ≃⟨ {! !} ⟩
  (Σ[ G ∈ Type ℓ ] StrictGroupoidStr G) ≃⟨⟩
  StrictGroupoid.ob ≃∎

isEquiv-Σˢ₀ : isEquiv Σˢ.₀
isEquiv-Σˢ₀ .equiv-proof H = goal where
  fiber-equiv : (fiber Σˢ.₀ H) ≃ Unit
  fiber-equiv =
    (fiber Σˢ.₀ H) ≃⟨⟩
    (Σ[ x ∈ Fam[hGroup].ob ] Σˢ.₀ x ≡ H) ≃⟨ Σ-assoc-≃ ⟩
    (Σ[ J ∈ hSet ℓ ] Σ[ G ∈ (⟨ J ⟩ → hGroup.ob) ] Σˢ.₀ (J , G) ≡ H) ≃⟨⟩
    (Σ[ J ∈ hSet ℓ ] Σ[ G ∈ (⟨ J ⟩ → hGroup.ob) ] StrictGroupoidΣSet J (fst ∘ G) ≡ H) ≃⟨ {! !} ⟩
    (Σ[ J ∈ hSet ℓ ] Σ[ G ∈ (⟨ J ⟩ → hGroup.ob) ] StrictGroupoidEquiv (StrictGroupoidΣSet J (fst ∘ G)) H) ≃⟨⟩
    (Σ[ J ∈ hSet ℓ ] Σ[ G ∈ (⟨ J ⟩ → hGroup.ob) ] Σ[ σ ∈ StrictFun (StrictGroupoidΣSet J (fst ∘ G)) H ] isEquiv (σ .fst)) ≃⟨ {! !} ⟩
    Unit ≃∎

  goal : isContr (fiber Σˢ.₀ H)
  goal = {! !}
-}

ε₀ : (G : StrictGroupoid.ob) → Σˢ.₀ (D₀ G) ≡ G
ε₀ G = uaStrict (Σˢ.₀ (D₀ G)) G $ mkStrictGroupoidEquiv (Σˢ.₀ (D₀ G)) G ε≃ is-strict-ε where
  module G = StrictGroupoidStr (str G)
  module ΣDG = StrictGroupoidStr (str (Σˢ.₀ (D₀ G)))

  ε≃ : ⟨ Σˢ.₀ (D₀ G) ⟩ ≃ ⟨ G ⟩
  ε≃ = invEquiv $ totalEquiv ∣_∣₂

  ε = equivFun ε≃

  is-strict-ε : ST.map ε ⋆ G.pt ≡ ΣDG.pt ⋆ ε
  is-strict-ε = funExt $ ST.elim (λ _ → G.is-groupoid _ _) $ uncurry goal where
    goal : (y : ∥ ⟨ G ⟩ ∥₂) → ((x , p) : fiber ∣_∣₂ y) → G.pt ∣ x ∣₂ ≡ G.pt y
    goal y (x , ∣x∣≡y) = cong G.pt ∣x∣≡y

ΣhGroupComponents≃ : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB}
  → isSet A
  → (∀ a → isPathConnected (B a))
  → ∥ Σ A B ∥₂ ≃ A
ΣhGroupComponents≃ {A} {B} is-set-A is-hgroup-B =
  ∥ Σ A B ∥₂ ≃⟨ setTruncateFstΣ≃ is-set-A ⟩
  Σ A (∥_∥₂ ∘ B) ≃⟨ Σ-contractSnd is-hgroup-B ⟩
  A ≃∎

η₀ : (x : Fam[hGroup].ob) → D₀ (Σˢ.₀ x) ≡ x
η₀ x@(J , G*) = Fam≡ ℓ hGroup (hSet≡ $ ua $ ΣhGroupComponents≃ (str J) is-connected-G) η₀-snd where
  G : ⟨ J ⟩ → StrictGroupoid.ob
  G = fst ∘ G*

  module G j = StrictGroupoidStr (str (G j))

  DΣG : ∥ Σ[ j ∈ ⟨ J ⟩ ] ⟨ G j ⟩ ∥₂ → StrictGroupoid.ob
  DΣG = GroupAt (Σˢ.₀ x)

  module DΣG x = StrictGroupoidStr (str (DΣG x))

  is-connected-G = snd ∘ G*

  module _ (j : ⟨ J ⟩) (g : ⟨ G j ⟩) where
    equivᴰ : (j′ : ⟨ J ⟩) (g′ : ⟨ G j′ ⟩) → _ ≃ _
    equivᴰ j′ g′ =
      Path (∥ Σ[ j ∈ ⟨ J ⟩ ] ⟨ G j ⟩ ∥₂) ∣ j′ , g′ ∣₂ ∣ j , g ∣₂ ≃⟨ PathSetTrunc≃PropTruncPath ⟩
      ∥ (j′ , g′) ≡ (j , g) ∥₁ ≃⟨ PT.propTrunc≃ $ invEquiv ΣPathP≃PathPΣ ⟩
      ∥ Σ[ p ∈ j′ ≡ j ] PathP (λ i → ⟨ G (p i) ⟩) g′ g ∥₁ ≃⟨ propTruncFstΣ≃ (str J j′ j) ⟩
      Σ[ p ∈ j′ ≡ j ] ∥ PathP (λ i → ⟨ G (p i) ⟩) g′ g ∥₁ ≃∎

    equiv : fiber ∣_∣₂ ∣ j , g ∣₂ ≃ ⟨ G j ⟩
    equiv =
      (Σ[ x ∈ Σ[ j ∈ ⟨ J ⟩ ] ⟨ G j ⟩ ] ∣ x ∣₂ ≡ ∣ j , g ∣₂) ≃⟨ Σ-assoc-≃ ⟩
      (Σ[ j′ ∈ ⟨ J ⟩ ] Σ[ g′ ∈ ⟨ G j′ ⟩ ] ∣ j′ , g′ ∣₂ ≡ ∣ j , g ∣₂) ≃⟨ Σ-cong-equiv-snd (λ j′ → Σ-cong-equiv-snd (equivᴰ j′)) ⟩
      (Σ[ j′ ∈ ⟨ J ⟩ ] Σ[ g′ ∈ ⟨ G j′ ⟩ ] Σ[ p ∈ j′ ≡ j ] ∥ PathP (λ i → ⟨ G (p i) ⟩) g′ g ∥₁) ≃⟨ shuffle ⟩
      (Σ[ (j′ , p) ∈ singl j ] Σ[ g′ ∈ ⟨ G j′ ⟩ ] ∥ PathP (λ i → ⟨ G (p (~ i)) ⟩) g′ g ∥₁) ≃⟨ Σ-contractFst (isContrSingl j) ⟩
      (Σ[ g′ ∈ ⟨ G j ⟩ ] ∥ g′ ≡ g ∥₁) ≃⟨ Σ-cong-equiv-snd (λ g′ → invEquiv PathSetTrunc≃PropTruncPath) ⟩
      (Σ[ g′ ∈ ⟨ G j ⟩ ] ∣ g′ ∣₂ ≡ ∣ g ∣₂) ≃⟨ Σ-contractSnd (λ g′ → isContr→isContrPath (is-connected-G j) _ _) ⟩
      ⟨ G j ⟩ ≃∎ where

      shuffle : _ ≃ _
      shuffle = strictEquiv
        (λ { (j′ , g′ , p , pᴰ) → ((j′ , sym p) , g′ , pᴰ) })
        (λ { ((j′ , p) , g′ , pᴰ) → (j′ , g′ , (sym p) , pᴰ) })

    f : fiber {A = Σ[ j ∈ ⟨ J ⟩ ] ⟨ G j ⟩} ∣_∣₂ ∣ j , g ∣₂ → ⟨ G j ⟩
    f ((j′ , g′) , p) = subst (λ - → ⟨ G - ⟩) {! !} g′

    is-strict-equiv : StrictFunStr (DΣG _) (G j) (equivFun equiv)
    is-strict-equiv = funExt $ ST.elim {! !} λ { ((j′ , g′) , p) → goal j′ g′ p } where
      goal : (j′ : ⟨ J ⟩) (g′ : ⟨ G j′ ⟩) (p : ∣ j′ , g′ ∣₂ ≡ ∣ j , g ∣₂)
        → G.pt j (ST.map (equivFun equiv) ∣ (j′ , g′) , p ∣₂) ≡ equivFun equiv (DΣG.pt ∣ j , g ∣₂ ∣ (j′ , g′) , p ∣₂)
      goal j′ g′ p =
        G.pt j (ST.map (equivFun equiv) ∣ (j′ , g′) , p ∣₂) ≡⟨⟩
        G.pt j (∣ equivFun equiv ((j′ , g′) , p) ∣₂) ≡⟨ {! !} ⟩
        equivFun equiv ((j , G.pt j ∣ g ∣₂) , {! !}) ≡⟨⟩
        equivFun equiv (DΣG.pt ∣ j , g ∣₂ ∣ (j′ , g′) , p ∣₂) ∎

    η₀-snd-ext : D₀ᴰ (Σˢ.₀ (J , G*)) ∣ j , g ∣₂ ≡ G* j
    η₀-snd-ext = hGroup≡ (uaStrict _ (G j) (mkStrictGroupoidEquiv (DΣG _) (G j) equiv is-strict-equiv))

  η₀-snd : PathP (λ i → ua (ΣhGroupComponents≃ (str J) is-connected-G) i → hGroup.ob) (D₀ᴰ (Σˢ.₀ (J , G*))) G*
  η₀-snd = ua→ $ ST.elim {! !} $ uncurry η₀-snd-ext

{-
D₁≡ : (x y : Fam[hGroup].ob) → Σˢ.₀ x ≡ Σˢ.₀ y → x ≡ y
D₁≡ x@(J , G*) y@(K , H) p = ΣPathP ({! cong fst p !} , {! !}) where
  G : ⟨ J ⟩ → StrictGroupoid.ob _
  G = fst ∘ G*
  test : (Σˢ.₀ x ≡ Σˢ.₀ y) ≃ {! !}
  test =
    Path (StrictGroupoid.ob ℓ) (Σˢ.₀ x) (Σˢ.₀ y) ≃⟨ univalenceStrict (Σˢ.₀ x) (Σˢ.₀ y) ⟩
    StrictGroupoidEquiv (Σˢ.₀ x) (Σˢ.₀ y) ≃⟨⟩
    Σ[ σ ∈ StrictFun (Σˢ.₀ x) (Σˢ.₀ y) ] _ ≃⟨ {!Σˢ.₀ x !} ⟩
    {! !} ≃∎

ε₁ : (x y : Fam[hGroup].ob) → section (cong {x = x} {y = y} Σˢ.₀) (D₁≡ x y)
ε₁ x y = {! !}

Σˢ₀-path-split-equiv : PathSplitEquiv Fam[hGroup].ob (StrictGroupoid.ob ℓ)
Σˢ₀-path-split-equiv .fst = Σˢ.₀
Σˢ₀-path-split-equiv .snd .isPathSplitEquiv.sec .fst = D₀
Σˢ₀-path-split-equiv .snd .isPathSplitEquiv.sec .snd = ε₀
Σˢ₀-path-split-equiv .snd .isPathSplitEquiv.secCong x y .fst = D₁≡ x y
Σˢ₀-path-split-equiv .snd .isPathSplitEquiv.secCong x y .snd = ε₁ x y

opaque
  isFullyFaithful-Σˢ : (x y : Fam[hGroup].ob) → isEquiv (Σˢ.₁ {x} {y})
  isFullyFaithful-Σˢ x y = {! (Σˢ.₁ {x} {y})!}

opaque
  isEquivalence-Σˢ : isEquivalence Σˢ
  isEquivalence-Σˢ = isFullyFaithful+isEquivF-ob→isEquiv isFullyFaithful-Σˢ isEquiv-Σˢ₀
  -}

{-
private
  η₀ : (x : Fam[hGroup].ob) → x ≡ D₀ (Σˢ ⟅ x ⟆)
  η₀ x@(J , G) = sym $ ΣPathP (hSet≡ (ua components-equiv) , ua→ {!  !}) where
    components-equiv : ∥ Σ[ j ∈ ⟨ J ⟩ ] hGroup.⌜ G j ⌝ ∥₂ ≃ ⟨ J ⟩
    components-equiv =
      ∥ Σ[ j ∈ ⟨ J ⟩ ] hGroup.⌜ G j ⌝ ∥₂ ≃⟨ setTruncateFstΣ≃ (str J) ⟩
      Σ[ j ∈ ⟨ J ⟩ ] ∥ hGroup.⌜ G j ⌝ ∥₂ ≃⟨ Σ-contractSnd (λ j → hGroup.is-connected (G j)) ⟩
      ⟨ J ⟩ ≃∎

    groups-path : (x : ∥ Σ[ j ∈ ⟨ J ⟩ ] hGroup.⌜ G j ⌝ ∥₂) → hGroupAt (Σˢ ⟅ J , G ⟆) x ≡ G (equivFun components-equiv x)
    groups-path = ST.elim (λ x → isGroupoidHGroup _ _) $ uncurry path
      where module _ (j : ⟨ J ⟩) (g : hGroup.⌜ G j ⌝) where
        equiv : fiber ∣_∣₂ ∣ j , g ∣₂ ≃ hGroup.⌜ G j ⌝
        equiv =
          (Σ[ x ∈ Σ[ j ∈ ⟨ J ⟩ ] hGroup.⌜ G j ⌝ ] ∣ x ∣₂ ≡ ∣ j , g ∣₂) ≃⟨ ? ⟩
          (Σ[ j′ ∈ ⟨ J ⟩ ] Σ[ g′ ∈ hGroup.⌜ G j ⌝ ] ∣ j′ , g′ ∣₂ ≡ ∣ j , g ∣₂) ≃⟨ ? ⟩
          hGroup.⌜ G j ⌝ ≃∎

        path : hGroupAt (Σˢ ⟅ J , G ⟆) ∣ j , g ∣₂ ≡ G j
        path = hGroup.ua equiv {! !}

  -- η₀ : (x : Fam[hGroup].ob) → x ≡ D₀ (Σˢ ⟅ x ⟆)
  -- η₀ x@(J , G) = ΣPathP (hSet≡ (ua components-equiv) , ua→ {! groups-path !}) where
  --   components-equiv : ⟨ J ⟩ ≃ ∥ Σ[ j ∈ ⟨ J ⟩ ] hGroup.⌜ G j ⌝ ∥₂
  --   components-equiv = invEquiv $
  --     ∥ Σ[ j ∈ ⟨ J ⟩ ] hGroup.⌜ G j ⌝ ∥₂ ≃⟨ setTruncateFstΣ≃ (str J) ⟩
  --     Σ[ j ∈ ⟨ J ⟩ ] ∥ hGroup.⌜ G j ⌝ ∥₂ ≃⟨ Σ-contractSnd (λ j → hGroup.is-connected (G j)) ⟩
  --     ⟨ J ⟩ ≃∎

  --   groups-path : ∀ j → G j ≡ hGroupAt (StrictGroupoidΣSet J (U₀ ∘ G)) (equivFun components-equiv j)
  --   groups-path j = hGroup.ua {G = G j} {H = hGroupAt (StrictGroupoidΣSet J (U₀ ∘ G)) (equivFun components-equiv j)} {! !} {! !}

  -- η₀ : (x : Fam[hGroup].ob) → Fam[hGroup] [ x , D₀ (Σˢ ⟅ x ⟆) ]
  -- η₀ x = {! !}

η : 𝟙⟨ Fam[hGroup] ⟩ ≅ᶜ D ∘F Σˢ
η .NT.NatIso.trans .NT.NatTrans.N-ob = {! !}
η .NT.NatIso.trans .NT.NatTrans.N-hom = {! !}
η .NT.NatIso.nIso = {! !}

inv-Σˢ : WeakInverse Σˢ
inv-Σˢ .WeakInverse.invFunc = D
inv-Σˢ .WeakInverse.η = NT.pathToNatIso (Functor≡ η₀ {! !})
inv-Σˢ .WeakInverse.ε = {! !}
-}
