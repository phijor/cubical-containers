{-# OPTIONS --lossy-unification #-}

open import GpdCont.Prelude

module GpdCont.SetBundle.Summation (ℓ : Level) where

open import GpdCont.SetBundle.Base ℓ

open import GpdCont.Univalence
open import GpdCont.SetTruncation using (componentEquiv ; setTruncateFstΣ≃ ; PathSetTrunc≃PropTruncPath)
open import GpdCont.Connectivity as Connectivity using (isPathConnected)

open import GpdCont.TwoCategory.Base using (TwoCategory)
open import GpdCont.TwoCategory.LaxFunctor using (LaxFunctor ; compLaxFunctor)
open import GpdCont.TwoCategory.LocalFunctor using (LocalFunctor)
open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryᴰ)
open import GpdCont.TwoCategory.Displayed.LocallyThin using (LocallyThinOver ; IntoLocallyThin)
open import GpdCont.TwoCategory.Displayed.LaxFunctor using (LaxFunctorᴰ)
open import GpdCont.TwoCategory.Displayed.Unit using (Unitᴰ ; UnitOver ; AddUnit ; ReindexUnit)
open import GpdCont.TwoCategory.Family.Base using (Fam ; Famᴰ ; Fam₂J[_] ; Famᴰ₂ ; Fam₂PathP)
open import GpdCont.TwoCategory.HomotopySet using (SetEq ; isTwoCategorySetStr)
open import GpdCont.TwoCategory.HomotopyGroupoid using (hGpdCat)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
import      Cubical.Foundations.Path as Path
import      Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Functions.FunExtEquiv as FunExt using (funExtEquiv)
open import Cubical.Functions.Surjection using (isSurjection ; _↠_ ; section→isSurjection)
open import Cubical.Categories.Functor using (Functor)
import      Cubical.Data.Sigma as Sigma
import      Cubical.Data.Equality as Eq
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

private
  module SetEq = TwoCategory (SetEq ℓ)
  module hGpdCat = TwoCategory (hGpdCat ℓ)

  module SetBundle where
    open SetBundleNotation public

  FamSetBundle : TwoCategory (ℓ-suc ℓ) ℓ ℓ
  FamSetBundle = Fam SetBundle ℓ

  module FamSetBundle where
    open TwoCategory FamSetBundle public
    open TwoCategoryᴰ (Famᴰ SetBundle ℓ) public

    ₂J[_] = Fam₂J[_] SetBundle ℓ

    relPathP = Fam₂PathP SetBundle ℓ

    relΣPathP : ∀ {x y} (f g : hom x y) → Type _
    relΣPathP {y} f g = (Σ[ p ∈ f .fst ≡ g .fst ] relPathP (y .snd) p (f .snd) (g .snd))

    rel≃ΣPathPᴰ : ∀ {x y : SetEq.ob} {f : SetEq.hom x y}
      → {xᴰ : ob[ x ]} (yᴰ : ob[ y ])
      → (fᴰ gᴰ : hom[ f ] xᴰ yᴰ)
      → Famᴰ₂ SetBundle ℓ yᴰ fᴰ gᴰ ≃ (fᴰ ≡ gᴰ)
    rel≃ΣPathPᴰ yᴰ fᴰ gᴰ = strictIsoToEquiv rel-iso where
      rel-iso : Iso (Famᴰ₂ SetBundle ℓ yᴰ fᴰ gᴰ) (fᴰ ≡ gᴰ)
      rel-iso .Iso.fun xs = funExt λ x₀ → Sigma.ΣPathP (xs x₀)
      rel-iso .Iso.inv fᴰ≡gᴰ x₀ = Sigma.PathPΣ (funExt⁻ fᴰ≡gᴰ x₀)
      rel-iso .Iso.leftInv _ = refl
      rel-iso .Iso.rightInv _ = refl

    rel≃ΣPathP : ∀ {x y} {f g : hom x y} → rel f g ≃ (Σ[ p ∈ f .fst ≡ g .fst ] relPathP (y .snd) p (f .snd) (g .snd))
    rel≃ΣPathP {y = y , yᴰ} {f = f , fᴰ} {g = g , gᴰ} = Sigma.Σ-cong-equiv
      (isoToEquiv $ invIso Eq.PathIsoEq)
      (λ { Eq.refl → rel≃ΣPathPᴰ yᴰ fᴰ gᴰ})

    rel≃PathPΣ : ∀ {x y} {f g : hom x y} → rel f g ≃ (f ≡ g)
    rel≃PathPΣ = rel≃ΣPathP ∙ₑ Sigma.ΣPathP≃PathPΣ

  ΣFst₀ : FamSetBundle.ob → hGpdCat.ob
  ΣFst₀ (J , X) .fst = Σ[ j ∈ ⟨ J ⟩ ] ⟨ SetBundle.Base (X j) ⟩
  ΣFst₀ (J , X) .snd = isGroupoidΣ (isSet→isGroupoid (str J)) λ j → SetBundle.isGroupoidBase (X j)
  {-# INJECTIVE_FOR_INFERENCE ΣFst₀ #-}

  ΣFst₁ : ∀ {X Y} → FamSetBundle.hom X Y → hGpdCat.hom (ΣFst₀ X) (ΣFst₀ Y)
  ΣFst₁ {X = _ , X} {Y = _ , Y} (φ , f) (j , b) .fst = φ j
  ΣFst₁ {X = _ , X} {Y = _ , Y} (φ , f) (j , b) .snd = SetBundle.homBase[ X j , Y (φ j) ] (f j) b
  {-# INJECTIVE_FOR_INFERENCE ΣFst₁ #-}

  ΣFst₂-ext : ∀ {J K} (φ : SetEq.hom J K) {X : FamSetBundle.ob[ J ]} {Y : FamSetBundle.ob[ K ]}
    (f g : FamSetBundle.hom[ φ ] X Y)
    → (rᴰ : ∀ j → f j .fst ≡ g j .fst)
    → (j : ⟨ J ⟩) (x : ⟨ X j .fst ⟩) → Path ⟨ ΣFst₀ (K , Y) ⟩ (φ j , f j .fst x) (φ j , g j .fst x)
  ΣFst₂-ext φ _ _ rᴰ j b = congS (λ f → φ j , f b) (rᴰ j)

  ΣFst₂ : ∀ {X Y} {f g : FamSetBundle.hom X Y}
    → FamSetBundle.rel {X} {Y} f g → Path (⟨ ΣFst₀ X ⟩ → ⟨ ΣFst₀ Y ⟩) (ΣFst₁ f) (ΣFst₁ g)
  ΣFst₂ {X = J , X} {f = φ , f} {g = .φ , g} (Eq.refl , rᴰ) = funExt $ λ { (j , b) → congS (λ - → φ j , - b) (rᴰ j .fst) }
  {-# INJECTIVE_FOR_INFERENCE ΣFst₂ #-}

  ΣFst₂-rel-trans : ∀ {X Y} {f g h : FamSetBundle.hom X Y}
    → (r : FamSetBundle.rel f g) (s : FamSetBundle.rel {y = Y} g h)
    → ΣFst₂ (r FamSetBundle.∙ᵥ s) ≡ ΣFst₂ r hGpdCat.∙ᵥ (ΣFst₂ s)
  ΣFst₂-rel-trans {X = J , X} {Y = K , Y} {f = φ , f} {g = ψ , g} {h = ρ , h} (Eq.refl , rᴰ) (Eq.refl , sᴰ) = funExtSquare (uncurry goal) where
    module _ (j : ⟨ J ⟩) (b : ⟨ SetBundle.Base (X j) ⟩) where
      goal :
        (congS (λ - → φ j , - b) (rᴰ j .fst ∙ sᴰ j .fst))
          ≡
        (congS (λ - → φ j , - b) (rᴰ j .fst)) ∙ (congS (λ - → φ j , - b) (sᴰ j .fst))
      goal = GL.cong-∙ (λ - → φ j , - b) (rᴰ j .fst) (sᴰ j .fst)

SetBundleΣFst : LaxFunctor FamSetBundle (hGpdCat ℓ)
SetBundleΣFst .LaxFunctor.F-ob = ΣFst₀
SetBundleΣFst .LaxFunctor.F-hom = ΣFst₁
SetBundleΣFst .LaxFunctor.F-rel = ΣFst₂
SetBundleΣFst .LaxFunctor.F-rel-id = refl
SetBundleΣFst .LaxFunctor.F-rel-trans = ΣFst₂-rel-trans
SetBundleΣFst .LaxFunctor.F-trans-lax (φ , f) (ψ , g) = refl
SetBundleΣFst .LaxFunctor.F-trans-lax-natural {x = J , X} {y = K , Y} {f₁ = φ , f₁} {f₂ = .φ , f₂} {g₁ = ψ , g₁} {g₂ = .ψ , g₂} (Eq.refl , rᴰ) (Eq.refl , sᴰ) = Path.Square→compPath
  λ where
    i j (idx , b) .fst → ψ (φ idx)
    i j (idx , b) .snd → sᴰ (φ idx) .fst i (rᴰ idx .fst i b)
SetBundleΣFst .LaxFunctor.F-id-lax (J , x) = refl
SetBundleΣFst .LaxFunctor.F-assoc (φ , f) (ψ , g) (ρ , h) = refl′ (refl ∙ refl)
SetBundleΣFst .LaxFunctor.F-unit-left (J , x) = sym GL.compPathRefl
SetBundleΣFst .LaxFunctor.F-unit-right (J , x) = sym GL.compPathRefl

private
  ΣSnd₀ : (x : FamSetBundle.ob) → SetBundle.ob[ ΣFst₀ x ]
  ΣSnd₀ (_ , X) (j , b) = SetBundle.Fiber (X j) b
  {-# INJECTIVE_FOR_INFERENCE ΣSnd₀ #-}

  ΣSnd₁ : ∀ {x y : FamSetBundle.ob} (f : FamSetBundle.hom x y) → SetBundle.hom[ ΣFst₁ {x} {y} f ] (ΣSnd₀ x) (ΣSnd₀ y)
  ΣSnd₁ (_ , f) (j , b) = f j .snd b
  {-# INJECTIVE_FOR_INFERENCE ΣSnd₁ #-}

  ΣSnd₂ : ∀ {x y : FamSetBundle.ob} {f g : FamSetBundle.hom x y}
    → (r : FamSetBundle.rel f g)
    → SetBundle.rel[_] {yᴰ = ΣSnd₀ y} (ΣFst₂ r) (ΣSnd₁ f) (ΣSnd₁ g)
  ΣSnd₂ (Eq.refl , rᴰ) = funExt λ (j , b) → rᴰ j .snd ≡$ b

SetBundleΣᵀ : IntoLocallyThin SetBundleΣFst (Unitᴰ FamSetBundle) SetBundleᵀ
SetBundleΣᵀ .IntoLocallyThin.F-obᴰ {x} _ = ΣSnd₀ x
SetBundleΣᵀ .IntoLocallyThin.F-homᴰ {x} {y} {f} _ = ΣSnd₁ {x} {y} f
SetBundleΣᵀ .IntoLocallyThin.F-relᴰ {r} _ = ΣSnd₂ r
SetBundleΣᵀ .IntoLocallyThin.F-trans-laxᴰ fᴰ gᴰ = refl
SetBundleΣᵀ .IntoLocallyThin.F-id-laxᴰ xᴰ = refl

SetBundleΣᴰ : LaxFunctorᴰ SetBundleΣFst (Unitᴰ FamSetBundle) SetBundleᴰ
SetBundleΣᴰ = IntoLocallyThin.toLaxFunctorᴰ SetBundleΣᵀ

SetBundleΣUnit : LaxFunctor (UnitOver FamSetBundle) SetBundle
SetBundleΣUnit = LaxFunctorᴰ.toTotalFunctor SetBundleΣᴰ

SetBundleΣ : LaxFunctor FamSetBundle SetBundle
SetBundleΣ = compLaxFunctor (AddUnit _) SetBundleΣUnit

private
  module SetBundleΣ where
    open LaxFunctor SetBundleΣ public

SetBundleΣ' : LaxFunctor FamSetBundle SetBundle
SetBundleΣ' = ReindexUnit FamSetBundle (hGpdCat ℓ) SetBundleΣFst SetBundleᴰ SetBundleΣᴰ

-- Local functors of Σ : Fam(SetBundle) → SetBundle are fully faithful whenever
-- the familiy x in Σ(x, y) : Fam(SetBundle)(x, y) → SetBundle(Σx, Σy) has a connected bases.
isLocallyFullyFaithfulΣ-at-connBase : (x @ (J , X) y : FamSetBundle.ob)
  → (conn-X : (j : ⟨ J ⟩) → isPathConnected ⟨ SetBundle.Base (X j) ⟩)
  → Functor.isFullyFaithful (LocalFunctor SetBundleΣ x y)
isLocallyFullyFaithfulΣ-at-connBase (J , X) (K , Y) conn-X (u , f) (v , g) = is-equiv-Σ₂ where
  -- The proof proceeds by showing that there is *some* equivalence of types of 2-cells
  --
  --    FamSetBundle₂((u, f), (v, g)) ≃ SetBundle₂(Σ₁(u, f), Σ₁(v, g))
  --
  -- whose underlying function is Σ₂.  This equivalence mostly shuffles Σ- and Π-types around.
  --
  -- The central insight is that paths between bases in the image of Σ really are
  -- paths between indexing functions and maps between bases at each index. We know
  -- that how Σ acts on such maps:
  _ : Σ[ u ∈ (⟨ J ⟩ → ⟨ K ⟩) ] (∀ j → SetBundle.hom (X j) (Y (u j)))
    ---------------------------------------------------------------------------------------
    → (Σ[ j ∈ ⟨ J ⟩ ] ⟨ SetBundle.Base (X j) ⟩) → (Σ[ k ∈ ⟨ K ⟩ ] ⟨ SetBundle.Base (Y k) ⟩)
  _ = ΣFst₁ {Y = _ , Y}
  -- Given some path (p : ΣFst₁ (u , f) ≡ ΣFst₁ (v , g)), we would like to extract a path (p′ : u ≡ v).
  -- The obvious idea (using `cong`), fails since it requires each base of Xⱼ to be pointed:
  _ : (p : ΣFst₁ {Y = _ , Y} (u , f) ≡ ΣFst₁ (v , g)) → (pt : ∀ j → ⟨ SetBundle.Base (X j) ⟩) → u ≡ v
  _ = λ p pt → cong (λ { u′ j → u′ (j , pt j) .fst }) p
  -- Even if this were the case, we'd have to ensure that the remaining construction did not depend
  -- on the choice of these points.
  --
  -- If instead we assume that for each (j : J) the base of Xⱼ is connected, we are able to extract
  -- such a path: ΣFst₁ maps a disjoint union of (now connected) spaces to some disjoint union of
  -- spaces. This assignment has to be continous, and from this we can extract where each connected
  -- component (indexed by J) goes.
  --
  -- In particular, a homotopy of maps of this type, (p : ΣFst₁ (u , f) ≡ ΣFst₁ (v , g)), has to
  -- preserve this assignment of indices.  Hence we obtain a path (u ≡ v) from p, where (u, v : J → K).

  -- This manifests in the below equivalence as follows: Maps from connected types into sets are
  -- constant [HoTT Book, 7.5.9], therefore at each (j : J), uⱼ ≡ vⱼ does not depend on (b : Base Xⱼ).
  connectivity-lemma : (j : ⟨ J ⟩) → (u j ≡ v j) ≃ (⟨ SetBundle.Base (X j) ⟩ → u j ≡ v j)
  connectivity-lemma j = Connectivity.isPathConnected→constEquiv
    (conn-X j)
    (isProp→isSet ((str K) _ _))

  relPathP-iso :
    Iso
      (Σ[ p ∈ u ≡ v ] FamSetBundle.relPathP Y p f g)
      (Σ[ (p , pᴰ) ∈ (Σ[ p ∈ u ≡ v ] PathP (λ i → (j : ⟨ J ⟩) → ⟨ SetBundle.Base (X j) ⟩ → ⟨ SetBundle.Base (Y (p i j)) ⟩) (fst ∘ f) (fst ∘ g)) ]
        (PathP (λ i → ∀ (j : ⟨ J ⟩) (b : ⟨ SetBundle.Base (X j) ⟩) → ⟨ SetBundle.Fiber (Y (p i j)) (pᴰ i j b) ⟩ → ⟨ SetBundle.Fiber (X j) b ⟩)
          (snd ∘ f)
          (snd ∘ g)
        )
      )
  relPathP-iso .Iso.fun (p , pᴰ) .fst .fst = p
  relPathP-iso .Iso.fun (p , pᴰ) .fst .snd i = λ j → pᴰ i j .fst
  relPathP-iso .Iso.fun (p , pᴰ) .snd i = λ j → pᴰ i j .snd
  relPathP-iso .Iso.inv ((p , pᴰ₁) , pᴰ₂) .fst = p
  relPathP-iso .Iso.inv ((p , pᴰ₁) , pᴰ₂) .snd i = λ j → pᴰ₁ i j , pᴰ₂ i j
  relPathP-iso .Iso.rightInv _ = refl
  relPathP-iso .Iso.leftInv _ = refl

  relPathP-equiv : _ ≃ _
  relPathP-equiv = strictIsoToEquiv relPathP-iso

  ΣFst₁-iso :
    Iso
      (Σ[ p ∈ u ≡ v ] PathP (λ i → (j : ⟨ J ⟩) → ⟨ SetBundle.Base (X j) ⟩ → ⟨ SetBundle.Base (Y (p i j)) ⟩) (fst ∘ f) (fst ∘ g))
      (ΣFst₁ (u , f) ≡ ΣFst₁ (v , g))
  ΣFst₁-iso =
    (Σ[ p ∈ u ≡ v ] PathP (λ i → (j : ⟨ J ⟩) → ⟨ SetBundle.Base (X j) ⟩ → ⟨ SetBundle.Base (Y (p i j)) ⟩) (fst ∘ f) (fst ∘ g))
      Iso⟨ funext-step ⟩
    (Σ[ p ∈ (∀ j → u j ≡ v j) ] ∀ j (b : ⟨ SetBundle.Base (X j) ⟩) → PathP (λ i → ⟨ SetBundle.Base (Y (p j i)) ⟩) (f j .fst b) (g j .fst b))
      Iso⟨ invIso Sigma.Σ-Π-Iso ⟩
    (∀ j → Σ[ p ∈ u j ≡ v j ] ∀ (b : ⟨ SetBundle.Base (X j) ⟩) → PathP (λ i → ⟨ SetBundle.Base (Y (p i)) ⟩) (f j .fst b) (g j .fst b))
      Iso⟨ connectivity-step ⟩ {- Connectivity of bases of ⟨ X j ⟩ is used here -}
    (∀ j → Σ[ p ∈ (⟨ SetBundle.Base (X j) ⟩ → u j ≡ v j) ] ∀ (b : ⟨ SetBundle.Base (X j) ⟩) → PathP (λ i → ⟨ SetBundle.Base (Y (p b i)) ⟩) (f j .fst b) (g j .fst b))
      Iso⟨ codomainIsoDep (λ j → invIso Sigma.Σ-Π-Iso) ⟩
    (∀ j (b : ⟨ SetBundle.Base (X j) ⟩) → Σ[ p ∈ u j ≡ v j ] PathP (λ i → ⟨ SetBundle.Base (Y (p i)) ⟩) (f j .fst b) (g j .fst b))
      Iso⟨ codomainIsoDep (λ j → codomainIsoDep (λ b → Sigma.ΣPathIsoPathΣ)) ⟩
    (∀ j (b : ⟨ SetBundle.Base (X j) ⟩) → Path (Σ[ k ∈ ⟨ K ⟩ ] ⟨ SetBundle.Base (Y k) ⟩) (u j , f j .fst b) (v j , g j .fst b))
      Iso⟨ invIso Sigma.curryIso ⟩
    (∀ x → ΣFst₁ (u , f) x ≡ ΣFst₁ (v , g) x)
      Iso⟨ FunExt.funExtIso ⟩
    (ΣFst₁ (u , f) ≡ ΣFst₁ (v , g))
      Iso∎ where

      funext-step : Iso _ _
      funext-step .Iso.fun = λ { (p , q) → (λ j i → p i j) , λ j b i → q i j b }
      funext-step .Iso.inv = λ { (p , q) → (λ i j → p j i) , λ i j b → q j b i }
      funext-step .Iso.rightInv = λ _ → refl
      funext-step .Iso.leftInv = λ _ → refl

      connectivity-step : Iso _ _
      connectivity-step = codomainIsoDep (λ j → Sigma.Σ-cong-iso-fst $ equivToIso (connectivity-lemma j))

  Σ₂-equiv : FamSetBundle.rel (u , f) (v , g) ≃ SetBundle.rel (SetBundleΣ.₁ (u , f)) (SetBundleΣ.₁ (v , g))
  Σ₂-equiv =
    FamSetBundle.rel (u , f) (v , g)
      ≃⟨⟩
    Σ[ p ∈ u Eq.≡ v ] FamSetBundle.rel[ p ] f g
      ≃⟨ FamSetBundle.rel≃ΣPathP ⟩
    Σ[ p ∈ u ≡ v ] FamSetBundle.relPathP Y p f g
      ≃⟨ relPathP-equiv ⟩
    Σ[ (p , pᴰ) ∈ (Σ[ p ∈ u ≡ v ] PathP (λ i → (j : ⟨ J ⟩) → ⟨ SetBundle.Base (X j) ⟩ → ⟨ SetBundle.Base (Y (p i j)) ⟩) (fst ∘ f) (fst ∘ g)) ]
      (PathP (λ i → ∀ (j : ⟨ J ⟩) (b : ⟨ SetBundle.Base (X j) ⟩) → ⟨ SetBundle.Fiber (Y (p i j)) (pᴰ i j b) ⟩ → ⟨ SetBundle.Fiber (X j) b ⟩) (snd ∘ f) (snd ∘ g))
      ≃⟨ Sigma.Σ-cong-equiv-snd (λ p → Path.congPathEquiv (λ _ → invEquiv Sigma.curryEquiv)) ⟩
    Σ[ (p , pᴰ) ∈ (Σ[ p ∈ u ≡ v ] PathP (λ i → (j : ⟨ J ⟩) → ⟨ SetBundle.Base (X j) ⟩ → ⟨ SetBundle.Base (Y (p i j)) ⟩) (fst ∘ f) (fst ∘ g)) ]
      (PathP (λ i → ((j , b) : Σ[ j ∈ ⟨ J ⟩ ] ⟨ SetBundle.Base (X j) ⟩) → ⟨ SetBundle.Fiber (Y (p i j)) (pᴰ i j b) ⟩ → ⟨ SetBundle.Fiber (X j) b ⟩)
        (uncurry (snd ∘ f))
        (uncurry (snd ∘ g))
      )
      ≃⟨ Sigma.Σ-cong-equiv-fst (isoToEquiv ΣFst₁-iso) ⟩
    Σ[ p ∈ ΣFst₁ (u , f) ≡ ΣFst₁ (v , g) ] SetBundle.rel[_] {yᴰ = ΣSnd₀ (K , Y)} p (ΣSnd₁ (u , f)) (ΣSnd₁ (v , g))
      ≃⟨⟩
    SetBundle.rel (SetBundleΣ.₁ (u , f)) (SetBundleΣ.₁ (v , g)) ≃∎

  Σ₂ : FamSetBundle.rel (u , f) (v , g) → SetBundle.rel (SetBundleΣ.₁ (u , f)) (SetBundleΣ.₁ (v , g))
  Σ₂ = SetBundleΣ.₂ {f = u , f} {g = v , g}

  Σ₂-equiv≡Σ₂ : equivFun Σ₂-equiv ≡ Σ₂
  Σ₂-equiv≡Σ₂ = funExt λ { (Eq.refl , rᴰ) → refl }

  is-equiv-Σ₂ : isEquiv Σ₂
  is-equiv-Σ₂ = subst isEquiv Σ₂-equiv≡Σ₂ (equivIsEquiv Σ₂-equiv)

SetBundleΣ₀⁻¹ : ∀ (X : SetBundle.ob) → FamSetBundle.ob
SetBundleΣ₀⁻¹ ((B , is-gpd-B) , F) = goal where
  S : hSet _
  S .fst = ∥ B ∥₂
  S .snd = ST.isSetSetTrunc

  B*-base : ⟨ S ⟩ → hGroupoid _
  B*-base s .fst = fiber ∣_∣₂ s
  B*-base s .snd = isGroupoidΣ is-gpd-B λ b → isProp→isOfHLevelSuc 2 (ST.isSetSetTrunc ∣ b ∣₂ s)

  B*-fib : (s : ⟨ S ⟩) → (⟨ B*-base s ⟩ → hSet _)
  B*-fib s = F ∘ fst

  B* : ⟨ S ⟩ → SetBundle.ob
  B* s .fst = B*-base s
  B* s .snd = B*-fib s

  goal : FamSetBundle.ob
  goal .fst = S
  goal .snd = B*

SetBundleΣ₀-section : section SetBundleΣ.₀ SetBundleΣ₀⁻¹
SetBundleΣ₀-section y@((B , _) , F) = sym (Sigma.ΣPathP (TypeOfHLevel≡ 3 base-path , fiber-path)) where
  base-path : B ≡ Σ ∥ B ∥₂ (fiber ∣_∣₂)
  base-path = ua (componentEquiv B)

  fiber-path : PathP (λ i → base-path i → hSet _) F (ΣSnd₀ (SetBundleΣ₀⁻¹ y))
  fiber-path = ua→ λ b → refl′ (F b)

isSurjection-SetBundleΣ₀ : isSurjection SetBundleΣ.₀
isSurjection-SetBundleΣ₀ = section→isSurjection SetBundleΣ₀-section

SetBundleΣ₀Surjection : FamSetBundle.ob ↠ SetBundle.ob
SetBundleΣ₀Surjection .fst = SetBundleΣ.₀
SetBundleΣ₀Surjection .snd = isSurjection-SetBundleΣ₀

SetBundleΣ₁⁻¹ : ∀ (X Y : SetBundle.ob) → SetBundle.hom X Y → FamSetBundle.hom (SetBundleΣ₀⁻¹ X) (SetBundleΣ₀⁻¹ Y)
SetBundleΣ₁⁻¹ X@((B , is-gpd-B) , F) Y@((D , is-gpd-D) , G) (u , f) = goal where
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
  ∣u∣ : ∥ B ∥₂ → ∥ D ∥₂
  ∣u∣ = ST.map u

  ∣f∣-base : (x : ∥ B ∥₂) → fiber ∣_∣₂ x → fiber ∣_∣₂ (∣u∣ x)
  ∣f∣-base x (b , ∣b∣≡x) .fst = u b
  ∣f∣-base x (b , ∣b∣≡x) .snd = cong ∣u∣ ∣b∣≡x

  ∣f∣-fib : (x : ∥ B ∥₂) → (x⁻¹ : fiber ∣_∣₂ x) → ⟨ G (u (x⁻¹ .fst)) ⟩ → ⟨ F (x⁻¹ .fst) ⟩
  ∣f∣-fib _ (b , _) = f b

  ∣f∣ : (x : ∥ B ∥₂) → SetBundle.hom (SetBundleΣ₀⁻¹ X .snd x) (SetBundleΣ₀⁻¹ Y .snd (∣u∣ x))
  ∣f∣ x .fst = ∣f∣-base x
  ∣f∣ x .snd = ∣f∣-fib x

  goal : FamSetBundle.hom (SetBundleΣ₀⁻¹ X) (SetBundleΣ₀⁻¹ Y)
  goal .fst = ∣u∣
  goal .snd = ∣f∣
