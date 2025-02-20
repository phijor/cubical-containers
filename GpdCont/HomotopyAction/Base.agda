open import GpdCont.Prelude

module GpdCont.HomotopyAction.Base (ℓ : Level) where

open import GpdCont.HomotopySet
open import GpdCont.HomotopyGroup ℓ as HomotopyGroup using (module hGroup) renaming (hGroupStrict to hGroup)
open import GpdCont.Connectivity
open import GpdCont.WildCat.TypeOfHLevel using (hGroupoidCat)
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.StrictFunctor
import      GpdCont.TwoCategory.GroupoidEndo as GroupoidEndo
open import GpdCont.TwoCategory.LocallyThin using (module FromCategory)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Instances.Functors.Endo using (EndofunctorCategory)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  EndoGpd = GroupoidEndo.Endo ℓ
  module EndoGpd = TwoCategory EndoGpd

Actionᴰ : Categoryᴰ hGroup (ℓ-suc ℓ) ℓ
Actionᴰ .Categoryᴰ.ob[_] G = hGroup.⌜ G ⌝ → hSet ℓ
Actionᴰ .Categoryᴰ.Hom[_][_,_] {x = G} {y = H} (φ , _) xᴰ yᴰ = (g : hGroup.⌜ G ⌝) → ⟨ yᴰ (φ g) ⟩ → ⟨ xᴰ g ⟩
Actionᴰ .Categoryᴰ.idᴰ = λ g → id _
Actionᴰ .Categoryᴰ._⋆ᴰ_ {f = (φ , _)} fᴰ gᴰ = λ x → fᴰ x ∘ gᴰ (φ x)
Actionᴰ .Categoryᴰ.⋆IdLᴰ _ = refl
Actionᴰ .Categoryᴰ.⋆IdRᴰ _ = refl
Actionᴰ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
Actionᴰ .Categoryᴰ.isSetHomᴰ {xᴰ} = isSetΠ2 λ g _ → str (xᴰ g)

Action : Category _ _
Action = ∫C Actionᴰ

Action∞ : TwoCategory _ _ _
Action∞ = FromCategory.LocallyThin Action

private
  module Action = Category Action
  module Action∞ = TwoCategory Action∞

⟦_⟧∞ : Action.ob → (Type ℓ → Type ℓ)
⟦ (G , σ) ⟧∞ X = Σ[ g ∈ hGroup.⌜ G ⌝ ] (⟨ σ g ⟩ → X)

isGroupoid-⟦-⟧∞ : ∀ {σ} {X} → isGroupoid X → isGroupoid (⟦ σ ⟧∞ X)
isGroupoid-⟦-⟧∞ is-gpd-X = isGroupoidΣ {! !} {! !}

⟦_⟧∞-map : ∀ (σ : Action.ob) {X Y : Type ℓ} → (f : X → Y) → ⟦ σ ⟧∞ X → ⟦ σ ⟧∞ Y
⟦ σ ⟧∞-map f = map-snd (_⋆ f)

⟦_⟧ : Action.ob → (Type ℓ → Type ℓ)
⟦ (G , σ) ⟧ X = ∥ Σ[ g ∈ hGroup.⌜ G ⌝ ] (⟨ σ g ⟩ → X) ∥₂

isSet-⟦-⟧ : ∀ (σ : Action.ob) {X : Type ℓ} → isSet (⟦ σ ⟧ X)
isSet-⟦-⟧ σ = ST.isSetSetTrunc

private
  EndoSet = EndofunctorCategory (SET ℓ)
  module EndoSet = Category EndoSet

⟦_⟧-map : ∀ (σ : Action.ob) {X Y : Type ℓ} → (f : X → Y) → ⟦ σ ⟧ X → ⟦ σ ⟧ Y
⟦ σ ⟧-map f = ST.map (map-snd (_⋆ f))

⟦_⟧₀ : Action.ob → EndoSet.ob
⟦_⟧₀ σ = F where
  F : Functor _ (SET _)
  F .Functor.F-ob X .fst = ⟦ σ ⟧ ⟨ X ⟩
  F .Functor.F-ob X .snd = isSet-⟦-⟧ σ
  F .Functor.F-hom = ⟦ σ ⟧-map
  F .Functor.F-id = funExt (ST.elim (λ _ → ST.isSetPathImplicit) λ _ → refl)
  F .Functor.F-seq f g = funExt (ST.elim (λ _ → ST.isSetPathImplicit) λ _ → refl)
  {-# INLINE F #-}

⟦_⟧₁ : ∀ {σ τ} → Action [ σ , τ ] → EndoSet [ ⟦ σ ⟧₀ , ⟦ τ ⟧₀ ]
⟦_⟧₁ {σ} {τ} ((φ , φ-eqva) , φᴰ) = nt where
  nt : ⟦ σ ⟧₀ ⇒ ⟦ τ ⟧₀
  nt .NatTrans.N-ob = λ X → ST.map λ (x , v) → φ x , φᴰ x ⋆ v
  nt .NatTrans.N-hom f = funExt (ST.elim (λ _ → ST.isSetPathImplicit) λ _ → refl)

⟦-⟧ : Functor Action EndoSet
⟦-⟧ .Functor.F-ob = ⟦_⟧₀
⟦-⟧ .Functor.F-hom = ⟦_⟧₁
⟦-⟧ .Functor.F-id = makeNatTransPath $ funExt λ X → funExt (ST.elim (λ _ → ST.isSetPathImplicit) λ _ → refl)
⟦-⟧ .Functor.F-seq f g = makeNatTransPath $ funExt λ X → funExt (ST.elim (λ _ → ST.isSetPathImplicit) λ _ → refl)

module ⟦-⟧ = Functor ⟦-⟧

⟦_⟧∞₀ : Action∞.ob → EndoGpd.ob
⟦ σ ⟧∞₀   .WildFunctor.F-ob X .fst = ⟦ σ ⟧∞ ⟨ X ⟩
⟦ σ ⟧∞₀   .WildFunctor.F-ob X .snd = isGroupoidΣ {! !} {! !}
⟦ σ ⟧∞₀   .WildFunctor.F-hom = ⟦ σ ⟧∞-map
⟦ σ ⟧∞₀   .WildFunctor.F-id = refl
⟦ σ ⟧∞₀   .WildFunctor.F-seq _ _ = refl

⟦_⟧∞₁ : ∀ {σ τ} → Action∞.hom σ τ → EndoGpd.hom ⟦ σ ⟧∞₀ ⟦ τ ⟧∞₀
⟦_⟧∞₁ {σ} {τ} ((φ , φ-eqva) , φᴰ) = nt where
  nt : WildNatTrans _ _ ⟦ σ ⟧∞₀ ⟦ τ ⟧∞₀
  nt .WildNatTrans.N-ob X (g , v) = φ g , φᴰ g ⋆ v
  nt .WildNatTrans.N-hom _ = refl

⟦-⟧∞ : StrictFunctor Action∞ EndoGpd
⟦-⟧∞ .StrictFunctor.F-ob = ⟦_⟧∞₀
⟦-⟧∞ .StrictFunctor.F-hom = ⟦_⟧∞₁
⟦-⟧∞ .StrictFunctor.F-rel = cong ⟦_⟧∞₁
⟦-⟧∞ .StrictFunctor.F-rel-id = refl
⟦-⟧∞ .StrictFunctor.F-rel-trans = cong-∙ ⟦_⟧∞₁
⟦-⟧∞ .StrictFunctor.F-hom-comp f g = {! !}
⟦-⟧∞ .StrictFunctor.F-hom-id = {! !}
⟦-⟧∞ .StrictFunctor.F-assoc-filler-left = {! !}
⟦-⟧∞ .StrictFunctor.F-assoc-filler-right = {! !}
⟦-⟧∞ .StrictFunctor.F-assoc = {! !}
⟦-⟧∞ .StrictFunctor.F-unit-left-filler = {! !}
⟦-⟧∞ .StrictFunctor.F-unit-left = {! !}
⟦-⟧∞ .StrictFunctor.F-unit-right-filler = {! !}
⟦-⟧∞ .StrictFunctor.F-unit-right = {! !}

inv-⟦_⟧∞₁ : ∀ {σ τ} → EndoGpd.hom ⟦ σ ⟧∞₀ ⟦ τ ⟧∞₀ → Action∞.hom σ τ
inv-⟦_⟧∞₁ {σ*@(G , σ)} {τ*@(H , τ)} nt = goal where
  open hGroup using (⌜_⌝ ; pt)
  open WildNatTrans nt renaming (N-ob to α ; N-hom to α-nat)

  φ : ⌜ G ⌝ → ⌜ H ⌝
  φ = {! α _ !}

  goal : Action∞.hom σ* τ*
  goal .fst .fst = φ
  goal .fst .snd = {! !}
  goal .snd = {! !}

private module _ {F G : EndoGpd.ob} where
  open WildFunctor F renaming (F-ob to F₀ ; F-hom to F₁)
  open WildFunctor G renaming (F-ob to G₀ ; F-hom to G₁)

  WildNatTransIsoΣ : Iso
    (WildNatTrans (hGroupoidCat ℓ) (hGroupoidCat ℓ) F G)
    (Σ[ α ∈ (∀ X → ⟨ F₀ X ⟩ → ⟨ G₀ X ⟩) ] ∀ {X Y} (f : ⟨ X ⟩ → ⟨ Y ⟩) → F₁ f ⋆ (α Y) ≡ (α X) ⋆ G₁ f)
  WildNatTransIsoΣ .Iso.fun α .fst = α .WildNatTrans.N-ob
  WildNatTransIsoΣ .Iso.fun α .snd = α .WildNatTrans.N-hom
  WildNatTransIsoΣ .Iso.inv (α-ob , α-hom) .WildNatTrans.N-ob = α-ob
  WildNatTransIsoΣ .Iso.inv (α-ob , α-hom) .WildNatTrans.N-hom = α-hom
  WildNatTransIsoΣ .Iso.rightInv (α-ob , α-hom) i .fst = α-ob
  WildNatTransIsoΣ .Iso.rightInv (α-ob , α-hom) i .snd = α-hom
  WildNatTransIsoΣ .Iso.leftInv α i .WildNatTrans.N-ob = α .WildNatTrans.N-ob
  WildNatTransIsoΣ .Iso.leftInv α i .WildNatTrans.N-hom = α .WildNatTrans.N-hom

  instance
    WildNatTransToΣ : RecordToΣ (WildNatTrans _ _ F G)
    WildNatTransToΣ .RecordToΣ.isoΣ = WildNatTransIsoΣ

-- charac-Im⟦-⟧∞ : ∀ σ τ → EndoGpd.hom ⟦ σ ⟧∞₀ ⟦ τ ⟧∞₀ ≃ Action∞.hom σ τ
-- charac-Im⟦-⟧∞ σ*@(G , σ) τ*@(H , τ) =
--   EndoGpd.hom ⟦ σ* ⟧∞₀ ⟦ τ* ⟧∞₀ ≃⟨⟩
--   WildNatTrans _ _ ⟦ σ* ⟧∞₀ ⟦ τ* ⟧∞₀ ≃⟨ {! !} ⟩
--   ((g : ⌜ G ⌝) → Σ[ h ∈ ⌜ H ⌝ ] (g ≡ pt G → h ≡ pt H) × (⟨ τ h ⟩ → ⟨ σ g ⟩)) ≃⟨ ? ⟩
--   Σ[ φ ∈ (⌜ G ⌝ → ⌜ H ⌝) ] (∀ g → g ≡ pt G → φ g ≡ pt H) × (∀ g → ⟨ τ (φ g) ⟩ → ⟨ σ g ⟩) ≃⟨ ? ⟩
--   Σ[ φ ∈ (⌜ G ⌝ → ⌜ H ⌝) ] (φ (pt G) ≡ pt H) × (∀ g → ⟨ τ (φ g) ⟩ → ⟨ σ g ⟩) ≃⟨ invEquiv Σ-assoc-≃ ⟩
--   Action∞.hom σ* τ* ≃∎
--   where
--     open hGroup using (⌜_⌝ ; pt)

-- isStrict-Im⟦-⟧∞ : ∀ σ τ → isSet (EndoGpd.hom ⟦ σ ⟧∞₀ ⟦ τ ⟧∞₀)
-- isStrict-Im⟦-⟧∞ σ τ = isOfHLevelRetract 2 inv-⟦_⟧∞₁ ⟦_⟧∞₁ {! !} Action.isSetHom
--

{-
untrunc : ∀ σ τ X → isGroupoid X → ∥ (⟦ σ ⟧∞ X → ⟦ τ ⟧∞ X) ∥₂ → (⟦ σ ⟧∞ X → ⟦ τ ⟧∞ X)
untrunc σ τ X is-gpd-X = ST.rec→Gpd.fun (isGroupoidΠ λ _ → isGroupoid-⟦-⟧∞ {σ = τ} is-gpd-X) (id _) {! !}

charac-conn-im : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} → isPathConnected X → isGroupoid Y → isSet (X → Y)
charac-conn-im {X} {Y} is-conn-X is-gpd-Y f g = {! !} where
  equiv : (f ≡ g) ≃ Unit
  equiv =
    (f ≡ g) ≃⟨ {! !} ⟩
    (∀ x → f x ≡ g x) ≃⟨ {! !} ⟩
    Unit ≃∎

module _ where
  open import Cubical.HITs.S1
  open import Cubical.Data.Unit
  nope : loop ≡ refl
  nope = isSetS1 _ _ _ _ where
    isSetS1 : isSet S¹
    isSetS1 = isOfHLevelRespectEquiv 2 (UnitToType≃ S¹) (charac-conn-im {! !} isGroupoidS¹)
-}

isConnectedUnit : isPathConnected (Unit* {ℓ})
isConnectedUnit .fst = ST.∣ tt* ∣₂
isConnectedUnit .snd = ST.elim (λ _ → ST.isSetPathImplicit) λ { tt* → refl }

UnitAction : Action.ob
UnitAction = (((Unit* , isOfHLevelUnit* 3) , tt*) , isConnectedUnit) , λ _ → UnitSet ℓ

⟦Unit⟧₁ : EndoGpd.hom ⟦ UnitAction ⟧∞₀ ⟦ UnitAction ⟧∞₀ ≃ Unit
⟦Unit⟧₁ =
  EndoGpd.hom ⟦ UnitAction ⟧∞₀ ⟦ UnitAction ⟧∞₀ ≃⟨ _ ≃Σ ⟩
  (Σ[ α ∈ ((X : hGroupoid ℓ) → ⟦ UnitAction ⟧∞ ⟨ X ⟩ → ⟦ UnitAction ⟧∞ ⟨ X ⟩) ] ∀ {X Y} (f : ⟨ X ⟩ → ⟨ Y ⟩) → ⟦ UnitAction ⟧∞-map f ⋆ (α Y) ≡ (α X) ⋆ ⟦ UnitAction ⟧∞-map f) ≃⟨ {! !} ⟩
  (Σ[ α ∈ ((X : hGroupoid ℓ) → ⟨ X ⟩ → ⟨ X ⟩) ] ∀ {X Y} (f : ⟨ X ⟩ → ⟨ Y ⟩) → f ⋆ (α Y) ≡ (α X) ⋆ f) ≃⟨ {! !} ⟩
  Unit ≃∎

{-
lemma₀ : ∀ σ τ (X : hGroupoid ℓ) → (⟦ σ ⟧∞ ⟨ X ⟩ → ⟦ τ ⟧∞ ⟨ X ⟩) ≃ Unit
lemma₀ σ*@(G , σ) τ*@(H , τ) (X , is-gpd-X) =
  (⟦ σ* ⟧∞ X → ⟦ τ* ⟧∞ X) ≃⟨⟩
  (Σ ⌜ G ⌝ (λ g → ⟨ σ g ⟩ → X) → ⟦ τ* ⟧∞ X) ≃⟨ {! !} ⟩
  ((g : ⌜ G ⌝) → (⟨ σ g ⟩ → X) → (Σ ⌜ H ⌝ (λ h → ⟨ τ h ⟩ → X))) ≃⟨ {! !} ⟩
  ((g : ⌜ G ⌝) → (Σ[ h* ∈ ((⟨ σ g ⟩ → X) → ⌜ H ⌝) ] ((v : ⟨ σ g ⟩ → X) → ⟨ τ (h* v) ⟩ → X))) ≃⟨ {! !} ⟩
  Unit ≃∎
  where
    open hGroup using (⌜_⌝ ; pt)

lemma : ∀ σ τ (X : hGroupoid ℓ) → isSet (⟦ σ ⟧∞ ⟨ X ⟩ → ⟦ τ ⟧∞ ⟨ X ⟩)
lemma σ τ X f g p q = {! !}

charac-Im⟦-⟧∞' : ∀ σ τ → EndoGpd.hom ⟦ σ ⟧∞₀ ⟦ τ ⟧∞₀ ≃ Unit
charac-Im⟦-⟧∞' σ*@(G , σ) τ*@(H , τ) =
  EndoGpd.hom ⟦ σ* ⟧∞₀ ⟦ τ* ⟧∞₀ ≃⟨⟩
  WildNatTrans (hGroupoidCat _) (hGroupoidCat _) ⟦ σ* ⟧∞₀ ⟦ τ* ⟧∞₀ ≃⟨ _ ≃Σ ⟩
  (Σ[ α ∈ ((X : hGroupoid ℓ) → ⟦ σ* ⟧∞ ⟨ X ⟩ → ⟦ τ* ⟧∞ ⟨ X ⟩) ] ∀ {X Y} (f : ⟨ X ⟩ → ⟨ Y ⟩) → ⟦ σ* ⟧∞-map f ⋆ (α Y) ≡ (α X) ⋆ ⟦ τ* ⟧∞-map f) ≃⟨ {! !} ⟩
  Unit ≃∎
  where
    open hGroup using (⌜_⌝ ; pt)

{-
isStrict-Im⟦-⟧∞' : ∀ σ τ → isSet (EndoGpd.hom ⟦ σ ⟧∞₀ ⟦ τ ⟧∞₀)
isStrict-Im⟦-⟧∞' σ τ = {! !}

⟦_⟧₁-inv : ∀ {σ τ} → EndoSet [ ⟦ σ ⟧₀ , ⟦ τ ⟧₀ ] → ∥ Action [ σ , τ ] ∥₁
⟦_⟧₁-inv {σ*@(G , σ)} {τ*@(H , τ)} α = {!α.N-ob (UnitSet _) !} where
  module α = NatTrans α
  -- eqva : Action [ σ* , τ* ]
  -- eqva .fst .fst = {! α.N-ob (UnitSet _) !}
  -- eqva .fst .snd = {! !}
  -- eqva .snd = {! !}

isFullyFaithful-⟦-⟧ : ⟦-⟧.isFullyFaithful
isFullyFaithful-⟦-⟧ σ τ = {! !}

private module _ {F G : EndoSet.ob} where
  NatTransIsoΣ : Iso
    (NatTrans F G)
    (Σ[ α ∈ (∀ X → ⟨ F ⟅ X ⟆ ⟩ → ⟨ G ⟅ X ⟆ ⟩) ] ∀ {X Y} (f : ⟨ X ⟩ → ⟨ Y ⟩) → F ⟪ f ⟫ ⋆ (α Y) ≡ (α X) ⋆ G ⟪ f ⟫)
  NatTransIsoΣ .Iso.fun (natTrans α α-nat) .fst = α
  NatTransIsoΣ .Iso.fun (natTrans α α-nat) .snd = α-nat
  NatTransIsoΣ .Iso.inv (α , α-nat) .NatTrans.N-ob = α
  NatTransIsoΣ .Iso.inv (α , α-nat) .NatTrans.N-hom = α-nat
  NatTransIsoΣ .Iso.rightInv _ = refl
  NatTransIsoΣ .Iso.leftInv _ = refl

  instance
    NatTransToΣ : RecordToΣ (NatTrans F G)
    NatTransToΣ .RecordToΣ.isoΣ = NatTransIsoΣ

ff-equiv : (σ τ : Action.ob) → NatTrans ⟦ σ ⟧₀ ⟦ τ ⟧₀ ≃ Action.Hom[ σ , τ ]
ff-equiv σ*@(G , σ) τ*@(H , τ) =
  NatTrans ⟦ σ* ⟧₀ ⟦ τ* ⟧₀ ≃⟨ _ ≃Σ ⟩
  (Σ[ α ∈ (∀ X → ⟨ ⟦ σ* ⟧₀ ⟅ X ⟆ ⟩ → ⟨ ⟦ τ* ⟧₀ ⟅ X ⟆ ⟩) ] ∀ {X Y} (f : ⟨ X ⟩ → ⟨ Y ⟩) → ⟦ σ* ⟧-map f ⋆ (α Y) ≡ (α X) ⋆ ⟦ τ* ⟧-map f) ≃⟨ {! !} ⟩
  (Σ[ α ∈ (∀ X → ∥ Σ[ g ∈ ⌜ G ⌝ ] (⟨ σ g ⟩ → ⟨ X ⟩) ∥₂ → ⟨ ⟦ τ* ⟧₀ ⟅ X ⟆ ⟩) ] ∀ {X Y} (f : ⟨ X ⟩ → ⟨ Y ⟩) → ⟦ σ* ⟧-map f ⋆ (α Y) ≡ (α X) ⋆ ⟦ τ* ⟧-map f) ≃⟨ {! !} ⟩
  ((g : ⌜ G ⌝) → Σ[ h ∈ ⌜ H ⌝ ] ((g ≡ pt G → h ≡ pt H) × (⟨ τ h ⟩ → ⟨ σ g ⟩))) ≃⟨ {! !} ⟩
  Σ[ φ ∈ (⌜ G ⌝ → ⌜ H ⌝) ] (∀ g → (g ≡ pt G → φ g ≡ pt H) × (⟨ τ (φ g) ⟩ → ⟨ σ g ⟩)) ≃⟨ {! !} ⟩
  Σ[ φ ∈ (⌜ G ⌝ → ⌜ H ⌝) ] (∀ g → g ≡ pt G → φ g ≡ pt H) × (∀ g → ⟨ τ (φ g) ⟩ → ⟨ σ g ⟩) ≃⟨ {! !} ⟩
  Σ[ φ ∈ (⌜ G ⌝ → ⌜ H ⌝) ] (φ (pt G) ≡ pt H) × (∀ g → ⟨ τ (φ g) ⟩ → ⟨ σ g ⟩) ≃⟨ invEquiv Σ-assoc-≃ ⟩
  Action.Hom[ σ* , τ* ] ≃∎
  where
    open hGroup using (⌜_⌝ ; pt)

isFull-⟦-⟧ : ⟦-⟧.isFull
isFull-⟦-⟧ = goal where module _ (σ τ : Action.ob) (α : NatTrans ⟦ σ ⟧₀ ⟦ τ ⟧₀) where
  open import Cubical.HITs.PropositionalTruncation.Monad

  goal : ∃[ f ∈ Action [ σ , τ ] ] ⟦ f ⟧₁ ≡ α
  goal = do
    {! !}
    -}
    -}
