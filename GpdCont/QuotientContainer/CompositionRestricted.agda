-- {-# OPTIONS --lossy-unification #-}
module GpdCont.QuotientContainer.CompositionRestricted where

open import GpdCont.Prelude
open import GpdCont.Prelude.Path
-- open import GpdCont.Prelude.Square
open import GpdCont.Equiv
open import GpdCont.Embedding
open import GpdCont.Univalence
open import GpdCont.HomotopySet
open import GpdCont.SetQuotients
-- import      GpdCont.Subuniverse
open import GpdCont.GroupAction.Base
-- open import GpdCont.GroupAction.Pi
-- open import GpdCont.GroupAction.Stabilizer using (module Setwise ; isPropIsStabilizer)
-- open import GpdCont.GroupAction.Equivariant
open import GpdCont.GroupAction.Faithful
open import GpdCont.Group.SymmetricGroup using (𝔖 ; symmConjGroupEquiv)
open import GpdCont.Group.Subgroup
-- open import GpdCont.Group.DirProd
-- open import GpdCont.Group.Pi using (ΠGroupEquiv)
open import GpdCont.Group.Opposite
open import GpdCont.Group.SemidirectProduct
-- open import GpdCont.Group.WreathProduct
-- open import GpdCont.Group.Equivs using (conjEquiv ; conjGroupEquiv)

open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Equiv.Properties using (cong≃ ; isPointedTarget→isEquiv→isEquiv)
open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Powerset as ℙ using (ℙ)
-- open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Foundations.Path using (compPathlEquiv ; congPathIso ; isProp→isPropPathP)
-- open import Cubical.Functions.Logic as Logic using (hProp≡)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Relation.Binary.Base
-- open import Cubical.Functions.Embedding
-- open import Cubical.Functions.Fibration
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Pi
-- open import Cubical.Algebra.Group.GroupPath using (isGroupoidGroup ; uaGroup)
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_])
-- open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)

[_⇒_]/_ : (X : hSet ℓ-zero) (Y : Type) {G : Group ℓ-zero} (σ : Action G X) → Type _
[_⇒_]/_ X Y {G} σ = (⟨ X ⟩ → Y) / λ f f' → ∃[ g ∈ ⟨ G ⟩ ] f ≡ f' ∘ equivFun (σ .Action.action g)

Pick : (A : Type) (R : A → A → Type) → Type
Pick A R = (A / R) → A

private
  variable
    ℓ : Level
    G H K : Group ℓ

  infixr 0 _≃⟨_⟩ᴳ_
  _≃⟨_⟩ᴳ_ : (G : Group ℓ) → GroupEquiv G H → GroupEquiv H K → GroupEquiv G K
  _≃⟨_⟩ᴳ_ _ e f = compGroupEquiv e f

  infix 1 _∎ᴳ
  _∎ᴳ : (G : Group ℓ) → GroupEquiv G G
  _∎ᴳ G = idGroupEquiv

{-
module Canon
  (S T : Type)
  (is-set-S : isSet S)
  (is-set-T : isSet T)
  (P : S → hSet ℓ-zero)
  (Q : T → hSet ℓ-zero)
  (G : S → Group ℓ-zero)
  (H : T → Group ℓ-zero)
  (σ : (s : S) → Action (G s) (P s))
  (is-faithful-σ : ∀ s → isFaithful (σ s))
  (τ : (t : T) → Action (H t) (Q t))
  (is-faithful-τ : ∀ t → isFaithful (τ t))
  where

  module σ {s} where
    open Action (σ s) public
    open ActionProperties (σ s) public

  module τ {t} where
    open Action (τ t) public
    open ActionProperties (τ t) public

  module G {s} = GroupStr (str (G s))
  module H {t} = GroupStr (str (H t))

  _≈_ : ∀ {s} → (f₀ f₁ : ⟨ P s ⟩ → T) → Type _
  f ≈ f' = Σ[ g ∈ ⟨ G _ ⟩ ] f ≡ f' ∘ (g σ.▷_)

  _∼_ : ∀ {s} → (f₀ f₁ : ⟨ P s ⟩ → T) → Type _
  f ∼ f' = ∥ f ≈ f' ∥₁

  module _ {s}
    (canon : ∀ (f f' : ⟨ P s ⟩ → T) → f ≈ f' → f ≈ f')
    (is-const-canon : ∀ {f f' : ⟨ P s ⟩ → T} → (r r' : f ≈ f') → canon f f' r ≡ canon f f' r')
    where
    private
      variable
        f f' : ⟨ P s ⟩ → T

    canon-∼ : f ∼ f' → f ≈ f'
    canon-∼ {f} {f'} = PT.rec→Set (isSetΣSndProp G.is-set (λ g → isSet→ is-set-T _ _)) (canon f f') $ is-const-canon {f} {f'}

    is-trans-≈ : BinaryRelation.isTrans (_≈_ {s})
    is-trans-≈ f₀ f₁ f₂ (g , eq) (g' , eq') .fst = g G.· g'
    is-trans-≈ f₀ f₁ f₂ (g , eq) (g' , eq') .snd = funExt λ p →
      f₀ p
        ≡⟨ eq ≡$ p ⟩
      f₁ (g σ.▷ p)
        ≡⟨ eq' ≡$ (g σ.▷ p) ⟩
      f₂ (g' σ.▷ (g σ.▷ p))
        ≡⟨ cong f₂ $ sym $ σ.action-comp-ext g g' p ⟩
      f₂ ((g G.· g') σ.▷ p)
        ∎

    is-trans-∼ : BinaryRelation.isTrans (_∼_ {s})
    is-trans-∼ f₀ f₁ f₂ = PT.map2 (is-trans-≈ f₀ f₁ f₂)

    -- canon-comp : ∀ f₀ f₁ f₂
    --   → (r : f₀ ∼ f₁)
    --   → (s : f₀ ∼ f₁)
    --   → is-trans-≈ f₀ f₁ f₂ (canon-∼ r) (canon- s) ≡ canon-∼ {f₀} {f₂} {! !}
    -- canon-comp = {! !}

    R* : (⟨ P s ⟩ → T) → hSet _
    R* f .fst = Σ[ t ∈ T ] (fiber f t) × ⟨ Q t ⟩
    R* f .snd = isSetΣ is-set-T λ t → isSet× (isSetΣSndProp (str $ P s) λ p → is-set-T (f p) t) (str $ Q t)

    opaque
      R∞-well-defined : f ≈ f' → R* f ≡ R* f'
      R∞-well-defined {f} {f'} (g , eq) = hSet≡ $ ua $ permute-Σ where
        permute-Σ : ⟨ R* f ⟩ ≃ ⟨ R* f' ⟩
        permute-Σ = Σ-cong-equiv-snd λ t → Σ-cong-equiv-fst (Σ-cong-equiv (σ.action g) (λ p → compPathlEquiv (sym (eq ≡$ p))))
      {-# INJECTIVE_FOR_INFERENCE R∞-well-defined #-}

    R*-well-defined : f ∼ f' → R* f ≡ R* f'
    R*-well-defined {f} {f'} r = R∞-well-defined {f} {f'} (canon-∼ {f} {f'} r)
    {-# INJECTIVE_FOR_INFERENCE R*-well-defined #-}

    R*-comp : ∀ {f₀ f₁ f₂ : ⟨ P s ⟩ → T}
      → (r : f₀ ∼ f₁)
      → (s : f₁ ∼ f₂)
      → R*-well-defined {f₀} {f₂} (is-trans-∼ f₀ f₁ f₂ r s) ≡ R*-well-defined r ∙ R*-well-defined {f' = f₂} s
    R*-comp {f₀} {f₁} {f₂} r s =
      R*-well-defined (is-trans-∼ f₀ f₁ f₂ r s)
        ≡⟨ {! !} ⟩
      (R*-well-defined r ∙ R*-well-defined {f' = f₂} s)
        ∎
    {-# INJECTIVE_FOR_INFERENCE R*-comp #-}

    R*-const : (r s : f ∼ f') → R*-well-defined {f} {f'} r ≡ R*-well-defined {f} {f'} s
    -- R*-const {f} {f'} r s = congS (R∞-well-defined {f} {f'}) {! !}
    -- R*-const {f} {f'} r s i j = R∞-well-defined {f} {f'} (canon-∼ {f} {f'} ?) j
    R*-const {f} {f'} r s i j = R*-well-defined {f} {f'} (PT.isPropPropTrunc r s i) j


    R : (⟨ P s ⟩ → T) / _∼_ → hSet _
    R = rec→Gpd' isGroupoidHSet is-trans-∼ R* R*-well-defined R*-comp R*-const

-}
module _
  (S T : Type)
  (is-set-S : isSet S)
  (is-set-T : isSet T)
  (P : S → hSet ℓ-zero)
  (Q : T → hSet ℓ-zero)
  (G : S → Group ℓ-zero)
  (H : T → Group ℓ-zero)
  (σ : (s : S) → Action (G s) (P s))
  (is-faithful-σ : ∀ s → isFaithful (σ s))
  (pick : ∀ {s} → Pick (⟨ P s ⟩ → T) λ f f' → ∃[ g ∈ ⟨ G s ⟩ ] f ≡ f' ∘ equivFun (σ s .Action.action g))
  (pick-section : ∀ {s} x → [ pick {s} x ] ≡ x)
  (τ : (t : T) → Action (H t) (Q t))
  (is-faithful-τ : ∀ t → isFaithful (τ t))
  where

  module σ {s} where
    open Action (σ s) public
    open ActionProperties (σ s) public

  module τ {t} where
    open Action (τ t) public
    open ActionProperties (τ t) public

  module G {s} = GroupStr (str (G s))
  module H {t} = GroupStr (str (H t))

  _∼_ : ∀ {s} → (f₀ f₁ : ⟨ P s ⟩ → T) → Type _
  f ∼ f' = ∃[ g ∈ ⟨ G _ ⟩ ] f ≡ f' ∘ (g σ.▷_)

  Sh : Type _
  Sh = Σ[ s ∈ S ] ((⟨ P s ⟩ → T) / _∼_)

  isSetSh : isSet Sh
  isSetSh = isSetΣ is-set-S λ s → SQ.squash/

  module * (s : S) (f : ⟨ P s ⟩ → T) where
    Ps* : hSet _
    Ps* .fst = Σ[ t ∈ T ] (fiber f t) × ⟨ Q t ⟩
    Ps* .snd = isSetΣ is-set-T λ t → isSet× (isSetΣSndProp (str $ P s) λ p → is-set-T (f p) t) (str $ Q t)

    Restrict : ⟨ G s ⟩ → Type _
    Restrict g = (t : T) (p : ⟨ P s ⟩) → (f p ≡ t) ≃ (f (g σ.▷ p) ≡ t)

    opaque
      isPropRestrict : ∀ g → isProp (Restrict g)
      isPropRestrict g = isPropΠ2 λ t p → isOfHLevel≃ 1 (is-set-T _ _) (is-set-T _ _)

      restrict-1g : Restrict G.1g
      restrict-1g t p = substEquiv (λ p' → f p' ≡ t) $ sym $ σ.action-1-id ≡$ p

      restrict-comp : ∀ {g h} → Restrict g → Restrict h → Restrict (g G.· h)
      restrict-comp {g} {h} rg rh t p =
        f p ≡ t
          ≃⟨ rg t p ⟩
        f (g σ.▷ p) ≡ t
          ≃⟨ rh t (g σ.▷ p) ⟩
        f (h σ.▷ (g σ.▷ p)) ≡ t
          ≃⟨ compPathlEquiv $ cong f (σ.action-comp-ext g h p) ⟩
        f ((g G.· h) σ.▷ p) ≡ t
          ≃∎

      restrict-inv : ∀ {g} → Restrict g → Restrict (G.inv g)
      restrict-inv {g} rg t p =
        f p ≡ t
          ≃⟨ compPathlEquiv $ cong f $ secEq (σ.action g) p ⟩
        f (g σ.▷ (g σ.▷⁻ p)) ≡ t
          ≃⟨ invEquiv $ rg t (g σ.▷⁻ p) ⟩
        f (g σ.▷⁻ p) ≡ t
          ≃⟨ compPathlEquiv $ cong f (σ.action-inv g ≡$ p) ⟩
        f (G.inv g σ.▷ p) ≡ t
          ≃∎

    G∣≤ : Subgroup (G s) _
    G∣≤ = isClosedSubset→Subgroup (G s) Restrict isPropRestrict restrict-1g restrict-comp restrict-inv

    G∣ : Group _
    G∣ = G∣≤ .fst

    module G∣ = GroupStr (str G∣)

    Fiber : T → hSet _
    Fiber t .fst = fiber f t
    Fiber t .snd = isSetΣSndProp (str $ P s) λ p → is-set-T (f p) t

    H∣ : Group _
    H∣ = ΠGroup {X = Σ[ t ∈ T ] fiber f t} λ (t , _) → H t

    σ∣ : ∀ t → Action G∣ (Fiber t)
    σ∣ t .Action.action (g , r) = Σ-cong-equiv (σ.action g) (r t)
    σ∣ t .Action.pres· (g , _) (h , _) = equivEq $ funExt λ (p , _) → Σ≡Prop (λ p → is-set-T (f p) t) $ σ.action-comp-ext g h p

    module σ∣ {t} where
      open Action (σ∣ t) public
      open ActionProperties (σ∣ t) public

    φ∣ : GroupHom (G∣ ᵒᵖ) (Aut H∣)
    φ∣ .fst g∣ .fst = equivΠDomain (Σ-cong-equiv-snd λ t → σ∣.action {t} g∣)
    φ∣ .fst g∣ .snd = makeIsGroupHom λ h₀ h₁ → refl
    φ∣ .snd = makeIsGroupHom λ g∣₀ g∣₁ → GroupEquiv≡ $ equivEq $ funExt₂ λ where
      h (t , p , fp≡t) → cong (λ - → h (t , -)) $ σ∣.action-comp-ext g∣₁ g∣₀ (p , fp≡t)

    Gr* : Group _
    Gr* = SemidirProd H∣ G∣ φ∣

    ac* : Action Gr* Ps*
    ac* .Action.action (h , g∣) = equiv where
      equiv : ⟨ 𝔖 Ps* ⟩
      equiv = Σ-cong-equiv-snd λ t → Σ-cong-equiv (σ∣.action {t} g∣) λ fib → (τ.action (h (t , fib)))
    ac* .Action.pres· (h₀ , g∣₀) (h₁ , g∣₁) = equivEq $ funExt λ where
      (t , fib , q) → ΣPathP λ where
        .fst → refl′ t
        .snd → ΣPathP λ where
          .fst → σ∣.action-comp-ext g∣₀ g∣₁ fib
          .snd → τ.action-comp-ext (h₀ (t , fib)) (h₁ (t , g∣₀ σ∣.▷ fib)) q

    module ac* = Action ac*

    isFaithful-ac* : (∀ p → ⟨ Q (f p) ⟩) → isFaithful ac*
    isFaithful-ac* sec {g = h₀ , g∣₀} {h = h₁ , g∣₁} htpy = ΣPathP λ where
      .fst → funExt λ where
        (t , fib) → is-faithful-τ t $ equivExt λ where
          q → rectify {A = T} {B = λ t → ⟨ Q t ⟩} is-set-T (cong (snd ∘ snd) $ funExt⁻ (cong equivFun htpy) (t , fib , q))
      .snd → Σ≡Prop isPropRestrict $ is-faithful-σ s $ equivExt λ p → cong (fst ∘ fst ∘ snd) (funExt⁻ (cong equivFun htpy) (f p , (p , refl) , sec p))

  Ps : Sh → hSet _
  Ps (s , x) = *.Ps* s $ pick x

  Gr : Sh → Group _
  Gr (s , x) = *.Gr* s $ pick x

  module UnitRight
    (is-contr-T : isContr T)
    (is-contr-Q : ∀ {t} → isContr ⟨ Q t ⟩)
    where
    private
      t₀ = is-contr-T .fst

      _≡t₀ = sym ∘ is-contr-T .snd

      q₀ : ∀ {t} → ⟨ Q t ⟩
      q₀ = is-contr-Q .fst

      is-triv-H : ∀ t → isContr ⟨ H t ⟩
      is-triv-H t = isFaithfulOnProp→isTrivial {σ = τ t} (is-faithful-τ t) $ isContr→isProp $ is-contr-Q

    sh-≃ : Sh ≃ S
    sh-≃ = Σ-contractSnd λ s → isContrRetract (λ _ _ → t₀) [_] (SQ.elimProp (λ x → SQ.squash/ _ _) (λ f → cong [_] $ funExt λ _ → is-contr-T .snd _)) (isContrΠ λ _ → is-contr-T)

    _ : equivFun sh-≃ ≡ fst
    _ = refl

    module _ (s : S) (f : ⟨ P s ⟩ → T) where
      open * s f

      ps* : ⟨ P s ⟩ ≃ ⟨ Ps* ⟩
      ps* = invEquiv $
        Σ[ t ∈ T ] (fiber f t) × ⟨ Q t ⟩
          ≃⟨ Σ-contractFst is-contr-T ⟩
        (fiber f t₀) × ⟨ Q t₀ ⟩
          ≃⟨ Σ-contractSnd (λ _ → is-contr-Q) ⟩
        (fiber f t₀)
          ≃⟨ Σ-contractSnd (λ p → inhProp→isContr (f p ≡t₀) (is-set-T _ _)) ⟩
        ⟨ P s ⟩
          ≃∎

      ps*-β : equivFun ps* ≡ (λ p → (t₀ , (p , (f p ≡t₀)) , q₀))
      ps*-β = refl

      is-triv-H∣ : isContr ⟨ H∣ ⟩
      is-triv-H∣ = isContrΠ λ { (t , _) → is-triv-H t }

      is-full-G∣ : GroupEquiv G∣ (G s)
      is-full-G∣ .fst .fst = isSubgroup.inc-fun (G∣≤ .snd)
      is-full-G∣ .fst .snd .equiv-proof g = inhProp→isContr ((g , restrict-g) , refl) $ isEmbedding→hasPropFibers (isSubgroup.is-embedding-inc-fun (G∣≤ .snd)) g
        where
          restrict-g : Restrict g
          restrict-g t p = isContr→Equiv (isOfHLevelPath 0 is-contr-T _ _) (isOfHLevelPath 0 is-contr-T _ _)
      is-full-G∣ .snd = isSubgroup.is-hom (G∣≤ .snd)

      gr* : GroupEquiv Gr* (G s)
      gr* =
        SemidirProd H∣ G∣ φ∣
          ≃⟨ SemidirProdContrBot H∣ G∣ φ∣ is-triv-H∣ ⟩ᴳ
        G∣
          ≃⟨ is-full-G∣ ⟩ᴳ
        G s
          ∎ᴳ

    ps : ∀ sh → ⟨ P (equivFun sh-≃ sh) ⟩ ≃ ⟨ Ps sh ⟩
    ps (s , x) = ps* s $ pick x

    gr : ∀ sh → GroupEquiv (Gr sh) (G (equivFun sh-≃ sh))
    gr (s , x) = gr* s $ pick x

  module UnitLeft
    (is-contr-S : isContr S)
    (is-contr-P : ∀ {s} → isContr ⟨ P s ⟩)
    where
    private
      s₀ = is-contr-S .fst
      s₀≡_ = is-contr-S .snd


      p₀ : ∀ {s} → ⟨ P s ⟩
      p₀ = is-contr-P .fst

      _≡p₀ : ∀ {s} (p : ⟨ P s ⟩) → p ≡ p₀
      _≡p₀ = sym ∘ is-contr-P .snd

    sh-Iso : Iso Sh T
    sh-Iso .Iso.fun = uncurry λ s → SQ.rec is-set-T (_$ p₀) λ where
      f f' → ∃-rec (is-set-T _ _) λ where
        g f≡f'∘g → (f≡f'∘g ≡$ p₀) ∙ cong f' (_ ≡p₀)
    sh-Iso .Iso.inv t = s₀ , [ const t ]
    sh-Iso .Iso.sec t = refl′ t
    sh-Iso .Iso.ret = uncurry λ s → SQ.elimProp (λ _ → isSetSh _ _) goal module sh-Iso where
      module _ {s} (f : ⟨ P s ⟩ → T) where
        opaque
          quot-path-J : ∀ {s} (p : s₀ ≡ s) → (f : ⟨ P s ⟩ → T) → PathP (λ i → (⟨ P (p i) ⟩ → T) / _∼_) [ const (f p₀) ] [ f ]
          quot-path-J = J (λ s p → (f : ⟨ P s ⟩ → T) → PathP (λ i → (⟨ P (p i) ⟩ → T) / _∼_) [ const (f p₀) ] _) λ where
            f → cong [_] $ funExt λ p → cong f $ sym $ p ≡p₀

          quot-path : PathP (λ i → (⟨ P ((s₀≡ s) i) ⟩ → T) / _∼_) [ const (f p₀) ] [ f ]
          quot-path = quot-path-J (s₀≡ s) f

        goal : _
        goal = ΣPathP (s₀≡ s , quot-path)

    sh-≃ : Sh ≃ T
    sh-≃ = isoToEquiv sh-Iso
      -- Σ[ s ∈ S ] ((⟨ P s ⟩ → T) / _∼_)
      --   ≃⟨ {! !} ⟩
      -- ((⟨ P s₀ ⟩ → T) / _∼_)
      --   ≃⟨ pullbackQuotEquiv (Π-contractDom is-contr-P) ⟩
      -- (T / pullbackRel (invEq (Π-contractDom is-contr-P)) _∼_)
      --   ≃⟨ {! !} ⟩
      -- T
      --   ≃∎

    module _ (s : S) (f : ⟨ P s ⟩ → T) where
      open * s f

      ps*-≃ : ⟨ Q (f p₀) ⟩ ≃ ⟨ Ps* ⟩
      ps*-≃ = {! !}

    ps-≃ : ∀ sh → ⟨ Q (equivFun sh-≃ sh) ⟩ ≃ ⟨ Ps sh ⟩
    ps-≃ (s , x) = substEquiv (λ - → ⟨ Q - ⟩) lemma ∙ₑ (ps*-≃ s $ pick x)
    -- SQ.elim {! !} {! !} {! !} where
        where
          lemma : equivFun sh-≃ (s , x) ≡ pick x p₀
          lemma = {! !}
