{-# OPTIONS --lossy-unification #-}
module GpdCont.GroupAction.TwoCategory where

open import GpdCont.Prelude

open import GpdCont.GroupAction.Base using (Action ; _⁺_ ; module ActionProperties)
open import GpdCont.GroupAction.Equivariant renaming (isEquivariantMap[_][_,_] to isEquivariantMap)
open import GpdCont.Group.TwoCategory using (TwoGroup)
open import GpdCont.TwoCategory.Base using (TwoCategory)
open import GpdCont.TwoCategory.LocalCategory using (isLocallyStrict)
open import GpdCont.TwoCategory.HomotopySet using (hSetCat)
open import GpdCont.TwoCategory.Displayed.Base using (TwoCategoryᴰ ; TwoCategoryStrᴰ)
open import GpdCont.TwoCategory.Displayed.LocallyThin using (LocallyThinOver ; IsLocallyThinOver ; module TotalTwoCategory)

open import Cubical.Foundations.HLevels using (hSet ; isSet→ ; isSetΣ ; isSetΣSndProp)
open import Cubical.Algebra.Group.Base using (GroupStr)
open import Cubical.Algebra.Group.MorphismProperties using (isSetGroupHom)

module _ (ℓ : Level) where
  private
    module hSetCat = TwoCategory (hSetCat ℓ)
    module TwoGroup = TwoCategory (TwoGroup ℓ)

    GroupActionᴰ₀ : TwoGroup.ob → Type (ℓ-suc ℓ)
    GroupActionᴰ₀ G = Σ[ X ∈ hSet ℓ ] Action G X

    GroupActionᴰ₁ : ∀ {G H} (φ : TwoGroup.hom G H) → GroupActionᴰ₀ G → GroupActionᴰ₀ H → Type ℓ
    GroupActionᴰ₁ φ (X , σ) (Y , τ) = Σ[ f ∈ (⟨ Y ⟩ → ⟨ X ⟩) ] isEquivariantMap (φ , f) σ τ
    {-# INJECTIVE_FOR_INFERENCE GroupActionᴰ₁ #-}

    isSetGroupActionᴰ₁ : ∀ {G H} (φ : TwoGroup.hom G H) (Xᴳ : GroupActionᴰ₀ G) (Yᴴ : GroupActionᴰ₀ H) → isSet (GroupActionᴰ₁ φ Xᴳ Yᴴ)
    isSetGroupActionᴰ₁ φ (X , σ) (_ , τ) = isSetΣSndProp (isSet→ (str X)) λ f → isPropIsEquivariantMap (φ , f) σ τ

    GroupActionᴰ₂ : ∀ {G H} {φ ψ : TwoGroup.hom G H} {Xᴳ : GroupActionᴰ₀ G} {Yᴴ : GroupActionᴰ₀ H} → (r : TwoGroup.rel φ ψ) → GroupActionᴰ₁ φ Xᴳ Yᴴ → GroupActionᴰ₁ ψ Xᴳ Yᴴ → Type _
    GroupActionᴰ₂ {Yᴴ = Y , τ} (r , _) (f₁ , _) (f₂ , _) = f₁ ≡ f₂ ∘ (τ ⁺ r)

    isPropGroupActionᴰ₂ : ∀ {G H} {φ ψ : TwoGroup.hom G H} {Xᴳ : GroupActionᴰ₀ G} {Yᴴ : GroupActionᴰ₀ H} {r : TwoGroup.rel φ ψ}
      → (fᴰ : GroupActionᴰ₁ φ Xᴳ Yᴴ) → (gᴰ : GroupActionᴰ₁ ψ Xᴳ Yᴴ)
      → isProp (GroupActionᴰ₂ r fᴰ gᴰ)
    isPropGroupActionᴰ₂ {Xᴳ = X , _} fᴰ gᴰ = isSet→ (str X) _ _

  GroupActionᴰ₁PathP : ∀ {G H} {φ ψ : TwoGroup.hom G H}
    → {Xᴳ : GroupActionᴰ₀ G} {Yᴴ : GroupActionᴰ₀ H}
    → {p : φ ≡ ψ}
    → {fᴰ : GroupActionᴰ₁ φ Xᴳ Yᴴ}
    → {gᴰ : GroupActionᴰ₁ ψ Xᴳ Yᴴ}
    → PathP (λ i → ⟨ Yᴴ .fst ⟩ → ⟨ Xᴳ .fst ⟩) (fᴰ .fst) (gᴰ .fst)
    → PathP (λ i → GroupActionᴰ₁ (p i) Xᴳ Yᴴ) fᴰ gᴰ
  GroupActionᴰ₁PathP {p} q i .fst = q i
  GroupActionᴰ₁PathP {p} {fᴰ = f , f-eqva} {gᴰ = g , g-eqva} q i .snd = isProp→PathP {B = λ i → isEquivariantMap (p i , q i) _ _} (λ i → isPropIsEquivariantMap (p i , q i) _ _) f-eqva g-eqva i

  private
    id₁ : ∀ {G} (Xᴳ : GroupActionᴰ₀ G) → GroupActionᴰ₁ (TwoGroup.id-hom G) Xᴳ Xᴳ
    id₁ (X , σ) .fst = id ⟨ X ⟩
    id₁ (X , σ) .snd = isEquivariantMap-id σ

    _∙₁_ : ∀ {G H K} {φ : TwoGroup.hom G H} {ψ : TwoGroup.hom H K}
      → {Xᴳ : GroupActionᴰ₀ G} {Yᴴ : GroupActionᴰ₀ H} {Zᴷ : GroupActionᴰ₀ K}
      → (f : GroupActionᴰ₁ φ Xᴳ Yᴴ)
      → (g : GroupActionᴰ₁ ψ Yᴴ Zᴷ)
      → GroupActionᴰ₁ (φ TwoGroup.∙₁ ψ) Xᴳ Zᴷ
    _∙₁_ (f , f-eqva) (g , g-eqva) .fst = g ⋆ f
    _∙₁_ {φ} {ψ} (f , f-eqva) (g , g-eqva) .snd = isEquivariantMap-comp (φ , f) (ψ , g) _ _ _ f-eqva g-eqva

    id₂ : ∀ {G H} {φ : TwoGroup.hom G H} {Xᴳ : GroupActionᴰ₀ G} {Yᴴ : GroupActionᴰ₀ H} (f : GroupActionᴰ₁ φ Xᴳ Yᴴ) → GroupActionᴰ₂ (TwoGroup.id-rel φ) f f
    id₂ (f , f-eqva) = cong (f ∘_) $ sym (ActionProperties.action-1-id _)

    _∙ᵥ_ : ∀ {G H} {φ ψ ρ : TwoGroup.hom G H} {r : TwoGroup.rel φ ψ} {s : TwoGroup.rel ψ ρ}
      → {Xᴳ : GroupActionᴰ₀ G} {Yᴴ : GroupActionᴰ₀ H} {f : GroupActionᴰ₁ φ Xᴳ Yᴴ} {g : GroupActionᴰ₁ ψ Xᴳ Yᴴ} {h : GroupActionᴰ₁ ρ Xᴳ Yᴴ}
      → (rᴰ : GroupActionᴰ₂ r f g)
      → (sᴰ : GroupActionᴰ₂ s g h)
      → GroupActionᴰ₂ (TwoGroup.trans r s) f h
    _∙ᵥ_ {H} {r = r , _} {s = s , _} {Yᴴ = Y , τ} {f = f , _} {g = g , _} {h = h , _} rᴰ sᴰ = goal where
      open GroupStr (str H) using (_·_)
      goal : f ≡ h ∘ (τ ⁺ (r · s))
      goal =
        f ≡⟨ rᴰ ⟩
        g ∘ (τ ⁺ r) ≡⟨ cong (_∘ τ ⁺ r) sᴰ ⟩
        h ∘ (τ ⁺ s) ∘ (τ ⁺ r) ≡⟨ sym $ cong (h ∘_) (ActionProperties.action-comp τ r s) ⟩
        h ∘ (τ ⁺ (r · s)) ∎

    GroupActionStr : TwoCategoryStrᴰ (TwoGroup ℓ) _ _ _ GroupActionᴰ₀ GroupActionᴰ₁ GroupActionᴰ₂
    GroupActionStr .TwoCategoryStrᴰ.id-homᴰ = id₁
    GroupActionStr .TwoCategoryStrᴰ.comp-homᴰ = _∙₁_
    GroupActionStr .TwoCategoryStrᴰ.id-relᴰ = id₂
    GroupActionStr .TwoCategoryStrᴰ.transᴰ = _∙ᵥ_
    GroupActionStr .TwoCategoryStrᴰ.comp-relᴰ {y = H} {z = K}
      {f₁ = φ₁ , _} {f₂ = φ₂ , _}
      {g₁ = ψ₁ , _} {g₂ = ψ₂ , _}
      {r = r , _} {s = s , s-grp-conj}
      {yᴰ = Y , τ} {zᴰ = Z , ρ}
      {f₁ᴰ = f₁ᴰ , _} {f₂ᴰ = f₂ᴰ , _} {g₁ᴰ = g₁ᴰ , g₁ᴰ-eqva} {g₂ᴰ = g₂ᴰ , _} f₁ᴰ≡f₂ᴰ∘τr g₁ᴰ≡g₂ᴰ∘ρs = goal where
      open GroupStr (str H) renaming (_·_ to _·ᴴ_)
      open GroupStr (str K) renaming (_·_ to _·ᴷ_)

      goal : f₁ᴰ ∘ g₁ᴰ ≡ f₂ᴰ ∘ g₂ᴰ ∘ (ρ ⁺ (s ·ᴷ ψ₂ r))
      goal =
        f₁ᴰ ∘ g₁ᴰ                         ≡[ i ]⟨ f₁ᴰ≡f₂ᴰ∘τr i ∘ g₁ᴰ ⟩
        --    --- r is a conjugator of f₁ and f₂
        --    -----------
        f₂ᴰ ∘ (τ ⁺ r) ∘ g₁ᴰ               ≡[ i ]⟨ f₂ᴰ ∘ g₁ᴰ-eqva r i ⟩
        --    '-----------' g₁ᴰ is equivariant wrt. τ and ρ
        --    .--------------.
        f₂ᴰ ∘ g₁ᴰ ∘ ρ ⁺ (ψ₁ r)            ≡[ i ]⟨ f₂ᴰ ∘ g₁ᴰ≡g₂ᴰ∘ρs i ∘ ρ ⁺ (ψ₁ r) ⟩
        --    '-' s is a conjugator of g₁ and g₂
        --    .-----------.
        f₂ᴰ ∘ g₂ᴰ ∘ (ρ ⁺ s) ∘ ρ ⁺ (ψ₁ r)  ≡[ i ]⟨ f₂ᴰ ∘ g₂ᴰ ∘ ActionProperties.action-comp ρ (ψ₁ r) s (~ i) ⟩
        --          '------------------' ρ preserves composition
        --          .-------------.
        f₂ᴰ ∘ g₂ᴰ ∘ ρ ⁺ (ψ₁ r ·ᴷ s)       ≡[ i ]⟨ f₂ᴰ ∘ g₂ᴰ ∘ ρ ⁺ s-grp-conj r i ⟩
        --              |---------| s is a conjugator of ψ₁ and ψ₂
        f₂ᴰ ∘ g₂ᴰ ∘ ρ ⁺ (s ·ᴷ ψ₂ r) ∎

  GroupActionᵀ : LocallyThinOver (TwoGroup ℓ) (ℓ-suc ℓ) ℓ ℓ
  GroupActionᵀ .LocallyThinOver.ob[_] = GroupActionᴰ₀
  GroupActionᵀ .LocallyThinOver.hom[_] = GroupActionᴰ₁
  GroupActionᵀ .LocallyThinOver.rel[_] = GroupActionᴰ₂
  GroupActionᵀ .LocallyThinOver.two-category-structureᴰ = GroupActionStr
  GroupActionᵀ .LocallyThinOver.is-locally-thinᴰ = is-locally-thin where
    is-locally-thin : IsLocallyThinOver (TwoGroup ℓ) _ _ _ GroupActionᴰ₀ GroupActionᴰ₁ GroupActionᴰ₂ GroupActionStr
    is-locally-thin .IsLocallyThinOver.is-prop-relᴰ {s} = isPropGroupActionᴰ₂ {r = s}
    is-locally-thin .IsLocallyThinOver.comp-hom-assocᴰ _ _ _ = GroupActionᴰ₁PathP refl
    is-locally-thin .IsLocallyThinOver.comp-hom-unit-leftᴰ _ = GroupActionᴰ₁PathP refl
    is-locally-thin .IsLocallyThinOver.comp-hom-unit-rightᴰ _ = GroupActionᴰ₁PathP refl

  GroupActionᴰ : TwoCategoryᴰ (TwoGroup ℓ) (ℓ-suc ℓ) ℓ ℓ
  GroupActionᴰ = LocallyThinOver.toTwoCategoryᴰ GroupActionᵀ

  GroupAction : TwoCategory (ℓ-suc ℓ) ℓ ℓ
  GroupAction = TotalTwoCategory.∫ (TwoGroup ℓ) GroupActionᵀ

  isLocallyStrictGroupAction : isLocallyStrict GroupAction
  isLocallyStrictGroupAction x y = isSetΣ isSetGroupHom λ φ → isSetGroupActionᴰ₁ φ (x .snd) (y .snd)
