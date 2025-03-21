{-# OPTIONS --lossy-unification #-}
open import GpdCont.Prelude hiding (_▷_)

module GpdCont.ActionContainer.Substitution (ℓ : Level) {ℓIx} (Ix : Type ℓIx) where

open import GpdCont.HomotopySet
open import GpdCont.Equiv using (equivΠDomain ; Σ-cong-equiv-comp)
open import GpdCont.TwoCategory.StrictFunctor
open import GpdCont.ActionContainer.Parametrized ℓ
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Equivariant using (isEquivariantMap[_][_,_])
open import GpdCont.GroupAction.Pi using (ΠActionΣ)
open import GpdCont.GroupAction.Sum using (_⊎Action_)
open import GpdCont.GroupAction.TwoCategory using (GroupAction)
open import GpdCont.GroupAction.Orbit as Orbit using (OrbitSet)
open import GpdCont.Group.DirProd using (DirProd ; module DirProd ; mapSndHom)
open import GpdCont.Group.Pi using (mapΠGroup)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)

private
  postulate
    trustme : ∀ {ℓ} {A : Type ℓ} → A

  _×Group_ = DirProd

_[_]-defect : (F : ActCont[ Ix +1]) → (G : ActCont.ob Ix) → ActCont.ob Ix
F [ G ]-defect = F[G] where
  module F = ActCont+1₀ F
  module G = ActCont₀ G

  F[G] : ActCont.ob _
  F[G] .fst = ΣSet F.Shape λ s → (F.Free s →Set G.Shape)
  F[G] .snd (sꟳ , sᴳ) ix .fst = DirProd (F.Symm (param ix) sꟳ) (ΠGroup (G.Symm ix ∘ sᴳ))
  F[G] .snd (sꟳ , sᴳ) ix .snd .fst = F.Param ix sꟳ ⊎Set ΣSet (F.Free sꟳ) (G.Pos ix ∘ sᴳ)
  F[G] .snd (sꟳ , sᴳ) ix .snd .snd = F.action (param ix) sꟳ ⊎Action ΠActionΣ (F.Free sꟳ) (G.Pos ix ∘ sᴳ) (G.action ix ∘ sᴳ)

_[_]₂ : (F : ActCont[ Ix +1]) → (G : ActCont.ob Ix) → ActCont.ob Ix
F [ G ]₂ = F[G] where
  module F = ActCont+1₀ F
  module G = ActCont₀ G

  module _ (sꟳ : ⟨ F.Shape ⟩) (sᴳ : ⟨ F.Free sꟳ ⟩ → ⟨ G.Shape ⟩) (ix : Ix) where
    Posᴰ : hSet _
    Posᴰ = Σ₂[ p ∈ F.Free sꟳ ] Π₂[ g ∈ ⟨ F.Symm free sꟳ ⟩ ] (G.Pos ix (sᴳ (g F.▷ p)))

    Pos : hSet _
    Pos = F.Param ix sꟳ ⊎Set Posᴰ

    Symmᴰ : Group _
    Symmᴰ = F.Symm free sꟳ ×Group ΠGroup {X = ⟨ F.Free sꟳ ⟩} (G.Symm ix ∘ sᴳ)

    Symm : Group _
    Symm = F.Symm (param ix) sꟳ ×Group Symmᴰ

    actionᴰ≃ : (f : ⟨ F.Symm free sꟳ ⟩) → (g : ∀ p → ⟨ G.Symm ix (sᴳ p) ⟩) → ⟨ Posᴰ ⟩ ≃ ⟨ Posᴰ ⟩
    actionᴰ≃ f g = Σ-cong-equiv on-fst on-snd-explicit where
      on-fst : ⟨ F.Free sꟳ ⟩ ≃ ⟨ F.Free sꟳ ⟩
      on-fst = F.action≃ free sꟳ f

      on-snd : ∀ p → (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ p)) ⟩) ≃ (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ (f F.▷ p))) ⟩)
      on-snd p .fst q f′ = g (f′ F.▷ (f F.▷ p)) G.▷ subst (λ p → ⟨ G.Pos ix (sᴳ p) ⟩) (F.·-▷-assoc f f′ p) (q (f F.· f′))
      on-snd p .snd = {! !}

      on-snd-explicit : ∀ p → (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ p)) ⟩) ≃ (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ (f F.▷ p))) ⟩)
      on-snd-explicit p =
        (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ p)) ⟩) ≃⟨ equivΠDomain (f F.·_ , {! !}) ⟩
        (∀ f′ → ⟨ G.Pos ix (sᴳ ((f F.· f′) F.▷ p)) ⟩) ≃⟨ equivΠCod (λ f′ → substEquiv (λ p → ⟨ G.Pos ix (sᴳ p) ⟩) (F.·-▷-assoc f f′ p)) ⟩
        (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ (f F.▷ p))) ⟩) ≃⟨ equivΠCod (λ f′ → G.action≃ ix (sᴳ _) (g _)) ⟩
        (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ (f F.▷ p))) ⟩) ≃∎

      test : ∀ p → on-snd p ≡ on-snd-explicit p
      test p = equivEq refl

      -- on-snd : ∀ p → (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ p)) ⟩) ≃ (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ (f F.▷ p))) ⟩)
      -- on-snd p = equivΠCod λ f′ → G.action≃ ix (sᴳ (f′ F.▷ p)) (g (f′ F.▷ p)) ∙ₑ {! !}

      -- TODO: It also seems to be possible to first "undo f" and then act:
      -- on-snd : ∀ p → (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ p)) ⟩) ≃ (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ (f F.▷ p))) ⟩)
      -- on-snd p = equivΠ (F._· (F.inv f) , {! !}) λ f′ → {! !}

    actionᴰ : Action Symmᴰ Posᴰ
    actionᴰ .Action.action = uncurry actionᴰ≃
    actionᴰ .Action.pres· (f₀ , g₀) (f₁ , g₁) = cong₂ Σ-cong-equiv (F.action free sꟳ .Action.pres· f₀ f₁) (funExt λ pos → equivPathP {! !}) ∙ Σ-cong-equiv-comp (F.action≃ free sꟳ f₀) (F.action≃ free sꟳ f₁) {! !} {! !}

    actionᴰ≃' : (f : ⟨ F.Symm free sꟳ ⟩) → (g : ∀ p → ⟨ G.Symm ix (sᴳ p) ⟩) → ⟨ Posᴰ ⟩ ≃ ⟨ Posᴰ ⟩
    actionᴰ≃' f g = Σ-cong-equiv-snd on-snd where
      on-snd : (p : ⟨ F.Free sꟳ ⟩) → (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ p)) ⟩) ≃ (∀ f′ → ⟨ G.Pos ix (sᴳ (f′ F.▷ p)) ⟩)
      on-snd p = equivΠCod λ f′ → {! !}

    action : Action Symm Pos
    action = F.action (param ix) sꟳ ⊎Action actionᴰ


  F[G] : ActCont.ob _
  F[G] .fst = ΣSet F.Shape λ s → (F.Free s →Set G.Shape)
  F[G] .snd (sꟳ , sᴳ) ix .fst = Symm sꟳ sᴳ ix
  F[G] .snd (sꟳ , sᴳ) ix .snd .fst = Pos sꟳ sᴳ ix
  F[G] .snd (sꟳ , sᴳ) ix .snd .snd = action sꟳ sᴳ ix

{-
{-
module _ {ℓ ℓ'} {G : Group ℓ} {X : hSet ℓ} where
  isClassFun : ∀ (σ : Action G X) {Y : Type ℓ'} → (f : ⟨ X ⟩ → Y) → Type _
  isClassFun σ f = ∀ x g → f x ≡ f (g σ.▷ x) where
    module σ = Action σ

  isPropIsClassFun : ∀ {σ : Action G X} {Y : Type ℓ'} → isSet Y → (f : ⟨ X ⟩ → Y) → isProp (isClassFun σ f)
  isPropIsClassFun is-set-Y f = isPropΠ2 λ x g → is-set-Y (f x) _

  ClassFun : ∀ (σ : Action G X) (Y : Type ℓ') → Type _
  ClassFun σ Y = Σ[ f ∈ (⟨ X ⟩ → Y) ] isClassFun σ f

  isSetClassFun : ∀ {σ : Action G X} {Y : Type ℓ'} → isSet Y → isSet (ClassFun σ Y)
  isSetClassFun is-set-Y = isSetΣSndProp (isSet→ is-set-Y) (isPropIsClassFun is-set-Y)

  ClassFunSet : (σ : Action G X) (Y : hSet ℓ') → hSet _
  ClassFunSet σ (Y , is-set-Y) .fst = ClassFun σ Y
  ClassFunSet σ (Y , is-set-Y) .snd = isSetClassFun is-set-Y


module _ {ℓ} {G : Group ℓ} {X : hSet ℓ}
  {H : ⟨ X ⟩ → Group ℓ}
  {Y : ⟨ X ⟩ → hSet ℓ}
  (σ : Action G X)
  where
  private
    module σ = Action σ

  Actionᴰ : Type _
  Actionᴰ =
    Σ[ σᴰ ∈ (∀ {g x} → ⟨ H x ⟩ → ⟨ Y x ⟩ ≃ ⟨ Y (g σ.▷ x) ⟩) ]
      ((g g′ : ⟨ G ⟩) (x x′ : ⟨ X ⟩) → (h : ⟨ H x ⟩) (h′ : ⟨ H x′ ⟩) → {! σᴰ h  !})

  private module _ (σᴰ : Actionᴰ) (g : ⟨ G ⟩) (h : ∀ x → ⟨ H x ⟩) where
    on-fst : ⟨ X ⟩ ≃ ⟨ X ⟩
    on-fst = σ.action g

    on-snd : ∀ x → ⟨ Y x ⟩ ≃ ⟨ Y (g σ.▷ x) ⟩
    on-snd x = σᴰ .fst (h x)

    on-Σ : ⟨ ΣSet X Y ⟩ ≃ ⟨ ΣSet X Y ⟩
    on-Σ = Σ-cong-equiv on-fst on-snd

  ∫Action : (σᴰ : Actionᴰ) → Action (G ×Group ΠGroup H) (ΣSet X Y)
  ∫Action σᴰ .Action.action (g , h) = on-Σ σᴰ g h
  ∫Action σᴰ .Action.pres· (g , h) (g′ , h′) = equivEq $ funExt λ { (x , y) → ΣPathP ((ActionProperties.action-comp σ g g′ ≡$ x) , {! !}) }

OrbitActionΣ/ : ∀ {ℓ} {G : Group ℓ} {X : hSet ℓ}
  → (σ : Action G X)
  → (Y : ⟨ OrbitSet σ ⟩ → hSet ℓ)
  → {H : ⟨ X ⟩ → Group ℓ}
  → (τ : ∀ x → Action (H x) (Y Orbit.[ σ ∣ x ]))
  → Action (G ×Group ΠGroup H) (ΣSet X (Y ∘ Orbit.[ σ ∣_]))
OrbitActionΣ/ {G} {X} σ Y {H} τ = σ⋉τ where
  module G = GroupStr (str G)
  module σ = Action σ
  module H {x} = GroupStr (str (H x))
  module τ {x} = Action (τ x)

  ΠH : Group _
  ΠH = ΠGroup H
  module ΠH = GroupStr (str ΠH)

  Y[_] : ⟨ X ⟩ → hSet _
  Y[ x ] = Y Orbit.[ σ ∣ x ]

  fix-Y : ∀ g x → ⟨ Y[ x ] ⟩ → ⟨ Y[ g σ.▷ x ] ⟩
  fix-Y g x = subst (λ x → ⟨ Y x ⟩) (Orbit.act→≡ σ g x)

  module _ (g : ⟨ G ⟩) (h : ∀ x → ⟨ H x ⟩) where
    on-fst : ⟨ X ⟩ ≃ ⟨ X ⟩
    on-fst = σ.action g

    on-snd : ∀ x → ⟨ Y[ x ] ⟩ ≃ ⟨ Y[ g σ.▷ x ] ⟩
    on-snd x = τ.action (h x) ∙ₑ substEquiv (λ x → ⟨ Y x ⟩) (Orbit.act→≡ σ g x)

    on-Σ→ : ⟨ ΣSet X Y[_] ⟩ → ⟨ ΣSet X Y[_] ⟩
    on-Σ→ (x , y) = (g σ.▷ x) , fix-Y g x (h x τ.▷ y)

    on-Σ : ⟨ ΣSet X Y[_] ⟩ ≃ ⟨ ΣSet X Y[_] ⟩
    on-Σ = Σ-cong-equiv on-fst on-snd

  opaque
    comp-lemma : ∀ g g′ (h h′ : ⟨ ΠH ⟩) → on-Σ→ (g G.· g′) (h ΠH.· h′) ≡ on-Σ→ g h ⋆ on-Σ→ g′ h′
    comp-lemma g g′ h h′ i (x , y) = goal x y i where module _ (x : ⟨ X ⟩) (y : ⟨ Y[ x ] ⟩) where
      on-fst-path : Path ⟨ X ⟩ ((σ ⁺ (g G.· g′)) x) (((σ ⁺ g′) ∘ (σ ⁺ g)) x)
      on-fst-path = ActionProperties.action-comp σ g g′ ≡$ x

      on-snd-path : subst (λ x → ⟨ Y[ x ] ⟩) on-fst-path (fix-Y (g G.· g′) x ((h ΠH.· h′) x τ.▷ y)) ≡ fix-Y g′ (g σ.▷ x) {! !}
      on-snd-path = {! !}

      goal : on-Σ→ (g G.· g′) (h ΠH.· h′) (x , y) ≡ (on-Σ→ g h ⋆ on-Σ→ g′ h′) (x , y)
      goal = ΣPathP (on-fst-path , toPathP {! !})
      -- (x , y) i .fst → ActionProperties.action-comp σ g g′ i x
      -- (x , y) i .snd → toPathP {! !} i
        -- on-Σ→ (g G.· g′) (h ΠH.· h′) (x , y) ≡⟨⟩
        -- ((g G.· g′) σ.▷ x) , fix-Y (g G.· g′) x ((h x H.· h′ x) τ.▷ y) ≡⟨ {! !} ⟩
        -- (g′ σ.▷ (g σ.▷ x)) , fix-Y (g G.· g′) x ((h x H.· h′ x) τ.▷ y) ≡⟨ {! !} ⟩
        -- (on-Σ→ g h ⋆ on-Σ→ g′ h′) (x , y) ∎

  σ⋉τ : Action _ _
  σ⋉τ .Action.action (g , h) = on-Σ g h
  σ⋉τ .Action.pres· (g , h) (g′ , h′) = equivEq (comp-lemma g g′ h h′)
    -- $ funExt λ where
    -- (x , y) i .fst → ActionProperties.action-comp σ g g′ i x
    -- (x , y) i .snd → {! transport  !}

OrbitActionΣ : ∀ {ℓ} {G : Group ℓ} {X : hSet ℓ}
  → {H : ⟨ X ⟩ → Group ℓ}
  → {Y : ⟨ X ⟩ → hSet ℓ}
  → (σ : Action G X)
  → (τ : ∀ x → Action (H x) (Y x))
  → isClassFun σ Y
  → Action (G ×Group ΠGroup H) (ΣSet X Y)
OrbitActionΣ {G} {X} {H} {Y} σ τ is-class-fun = σ⋉τ where
  module σ = Action σ
  module τ {x} = Action (τ x)

  module _ (g : ⟨ G ⟩) (h : ∀ x → ⟨ H x ⟩) where
    on-fst : ⟨ X ⟩ ≃ ⟨ X ⟩
    on-fst = σ.action g

    on-snd : ∀ x → ⟨ Y x ⟩ ≃ ⟨ Y (g σ.▷ x) ⟩
    on-snd x = τ.action (h x) ∙ₑ pathToEquiv (cong ⟨_⟩ (is-class-fun x g))

    on-Σ : ⟨ ΣSet X Y ⟩ ≃ ⟨ ΣSet X Y ⟩
    on-Σ = Σ-cong-equiv on-fst on-snd

  σ⋉τ : Action _ _
  σ⋉τ .Action.action (g , h) = on-Σ g h
  σ⋉τ .Action.pres· (g , h) (g′ , h′) = equivEq $ funExt λ where
    (x , y) i .fst → ActionProperties.action-comp σ g g′ i x
    (x , y) i .snd → {! transport  !}
-}

{-
_[_]-class-fun : (F : ActCont[ Ix +1]) → (G : ActCont.ob Ix) → ActCont.ob Ix
_[_]-class-fun F G = F[G] where
  module F = ActCont+1₀ F
  module G = ActCont₀ G

  Shape : hSet ℓ
  Shape = ΣSet F.Shape (λ sꟳ → ClassFunSet (F.action free sꟳ) G.Shape)

  module _ (ix : Ix) (sꟳ : ⟨ F.Shape ⟩) (sᴳ : ⟨ F.Free sꟳ ⟩ → ⟨ G.Shape ⟩) (class-fun : ∀ p g → (sᴳ p ≡ sᴳ (g F.▷ p))) where
    Pos : hSet ℓ
    Pos = F.Param ix sꟳ ⊎Set ΣSet (F.Free sꟳ) (G.Pos ix ∘ sᴳ)

    Symm : Group ℓ
    Symm = F.Symm (param ix) sꟳ ×Group (F.Symm free sꟳ ×Group (ΠGroup (G.Symm ix ∘ sᴳ)))

    is-class-fun* : isClassFun (F.action free sꟳ) (G.Pos ix ∘ sᴳ)
    is-class-fun* pꟳ gꟳ = cong (G.Pos ix) (class-fun pꟳ gꟳ)

    actionᴰ : Action (F.Symm free sꟳ ×Group (ΠGroup (G.Symm ix ∘ sᴳ))) (ΣSet (F.Free sꟳ) (G.Pos ix ∘ sᴳ))
    actionᴰ = OrbitActionΣ {Y = G.Pos ix ∘ sᴳ} (F.action free sꟳ) (G.action ix ∘ sᴳ) is-class-fun*

    action : Action Symm Pos
    action = F.action (param ix) sꟳ ⊎Action actionᴰ

  F[G] : ActCont.ob _
  F[G] .fst = Shape
  F[G] .snd (sꟳ , sᴳ , class-fun) ix .fst = Symm ix sꟳ sᴳ class-fun
  F[G] .snd (sꟳ , sᴳ , class-fun) ix .snd .fst = Pos ix sꟳ sᴳ class-fun
  F[G] .snd (sꟳ , sᴳ , class-fun) ix .snd .snd = action ix sꟳ sᴳ class-fun

_[_]-wrong-positions : (F : ActCont[ Ix +1]) → (G : ActCont.ob Ix) → ActCont.ob Ix
_[_]-wrong-positions F G = F[G] where
  module F = ActCont+1₀ F
  module G = ActCont₀ G

  Shape : hSet ℓ
  Shape = ΣSet F.Shape (λ sꟳ → F.Free/ sꟳ →Set G.Shape)

  module _ (ix : Ix) (sꟳ : ⟨ F.Shape ⟩) (sᴳ : ⟨ F.Free/ sꟳ ⟩ → ⟨ G.Shape ⟩) where
    open Orbit (F.action free sꟳ) using ([_])

    [sᴳ] : ⟨ F.Free sꟳ ⟩ → ⟨ G.Shape ⟩
    [sᴳ] = sᴳ ∘ [_]

    Pos : hSet ℓ
    Pos = F.Param ix sꟳ ⊎Set ΣSet (F.Free sꟳ) (G.Pos ix ∘ [sᴳ])

    Symm : Group ℓ
    Symm = F.Symm (param ix) sꟳ ×Group (F.Symm free sꟳ ×Group (ΠGroup (G.Symm ix ∘ [sᴳ])))

    actionᴰ : Action (F.Symm free sꟳ ×Group ΠGroup (G.Symm ix ∘ [sᴳ])) (ΣSet (F.Free sꟳ) (G.Pos ix ∘ [sᴳ]))
    actionᴰ = OrbitActionΣ/ (F.action free sꟳ) (G.Pos ix ∘ sᴳ) {H = G.Symm ix ∘ [sᴳ]} (G.action ix ∘ [sᴳ])

    action : Action Symm Pos
    action = F.action (param ix) sꟳ ⊎Action actionᴰ

  F[G] : ActCont.ob _
  F[G] .fst = Shape
  F[G] .snd (sꟳ , sᴳ) ix .fst = Symm ix sꟳ sᴳ
  F[G] .snd (sꟳ , sᴳ) ix .snd .fst = Pos ix sꟳ sᴳ
  F[G] .snd (sꟳ , sᴳ) ix .snd .snd = action ix sꟳ sᴳ
  -}

_[_] : (F : ActCont[ Ix +1]) → (G : ActCont.ob Ix) → ActCont.ob Ix
_[_] F G = F[G] where
  module F = ActCont+1₀ F
  module G = ActCont₀ G

  Shape : hSet ℓ
  Shape = Σ₂[ sꟳ ∈ F.Shape ] (F.Free/ sꟳ →Set G.Shape)

  module _ (ix : Ix) (sꟳ : ⟨ F.Shape ⟩) (sᴳ : ⟨ F.Free/ sꟳ ⟩ → ⟨ G.Shape ⟩) where
    open Orbit (F.action free sꟳ) using ([_])

    [sᴳ] : ⟨ F.Free sꟳ ⟩ → ⟨ G.Shape ⟩
    [sᴳ] = sᴳ ∘ [_]

    Pos : hSet ℓ
    Pos = F.Param ix sꟳ ⊎Set (Σ₂[ pꟳ ∈ F.Free/ sꟳ ] G.Pos ix (sᴳ pꟳ))

    Symm : Group ℓ
    Symm = F.Symm (param ix) sꟳ ×Group (ΠGroup {X = ⟨ F.Free/ sꟳ ⟩} (G.Symm ix ∘ sᴳ))

    action : Action Symm Pos
    action = F.action (param ix) sꟳ ⊎Action ΠActionΣ (F.Free/ sꟳ) (G.Pos ix ∘ sᴳ) (G.action ix ∘ sᴳ)

  F[G] : ActCont.ob _
  F[G] .fst = Shape
  F[G] .snd (sꟳ , sᴳ) ix .fst = Symm ix sꟳ sᴳ
  F[G] .snd (sꟳ , sᴳ) ix .snd .fst = Pos ix sꟳ sᴳ
  F[G] .snd (sꟳ , sᴳ) ix .snd .snd = action ix sꟳ sᴳ

{-
_[_]′ : (F : ActCont[ Ix +1]) → (G : ActCont.ob Ix) → ActCont.ob Ix
_[_]′ {Ix} F G = F[G]′ where
  module F = ActCont+1₀ F
  module G = ActCont₀ G

  SubstShapeᴰ : ⟨ F.Shape ⟩ → hSet _
  SubstShapeᴰ sꟳ = ⟨ F.Free sꟳ →Set G.Shape ⟩ /Set F._∼_

  SubstShape : hSet _
  SubstShape = ΣSet F.Shape SubstShapeᴰ

  module _ (ix : Ix) (sꟳ : ⟨ F.Shape ⟩) where

    SubstSymm' : (sᴳ : ⟨ F.Free sꟳ →Set G.Shape ⟩) → Group _
    SubstSymm' sᴳ = DirProd (F.Symm (param ix) sꟳ) (ΠGroup (G.Symm ix ∘ sᴳ))

    SubstSymm'-welldefined : ∀ (s₀ s₁ : ⟨ F.Free sꟳ →Set G.Shape ⟩) → s₀ F.∼ s₁ → SubstSymm' s₀ ≡ SubstSymm' s₁
    SubstSymm'-welldefined s₀ s₁ (gꟳ , p) = uaGroup (α , {! !}) where
      p' : (posꟳ : ⟨ F.Free sꟳ ⟩) → s₀ posꟳ ≡ s₁ (gꟳ F.▷ posꟳ)
      p' = ua→⁻ p

      lemma : (posꟳ : ⟨ F.Free sꟳ ⟩) → ⟨ G.Symm ix (s₀ posꟳ) ⟩ ≃ ⟨ G.Symm ix (s₁ posꟳ) ⟩
      lemma posꟳ .fst g₀ = transp (λ i → ⟨ G.Symm ix (p i (ua-gluePath (F.action≃ free sꟳ gꟳ) {x = posꟳ} {y = posꟳ} {! !} i)) ⟩) i0 g₀
      lemma posꟳ .snd = {! !}

      α : ⟨ SubstSymm' s₀ ⟩ ≃ ⟨ SubstSymm' s₁ ⟩
      α = Σ-cong-equiv-snd λ _ → equivΠCod lemma

    SubstSymm : (sᴳ : ⟨ SubstShapeᴰ sꟳ ⟩) → Group _
    SubstSymm = SQ.rec→Gpd.fun isGroupoidGroup SubstSymm' SubstSymm'-welldefined {! !}

    SubstPos' : (sᴳ : ⟨ F.Free sꟳ →Set G.Shape ⟩) → hSet _
    SubstPos' sᴳ = F.Param ix sꟳ ⊎Set ΣSet (F.Free sꟳ) λ posꟳ → G.Pos ix (sᴳ posꟳ)

    SubstPos'-welldefined : ∀ (s₀ s₁ : ⟨ F.Free sꟳ →Set G.Shape ⟩) → s₀ F.∼ s₁ → SubstPos' s₀ ≡ SubstPos' s₁
    SubstPos'-welldefined s₀ s₁ (gꟳ , p) = cong (F.Param ix sꟳ ⊎Set_) $ hSet≡ $ ua $ Σ-cong-equiv (F.action≃ free sꟳ gꟳ)
      λ posꟳ → the (⟨ G.Pos ix (s₀ posꟳ) ⟩ ≃ ⟨ G.Pos ix (s₁ (gꟳ F.▷ posꟳ)) ⟩)
        (substEquiv (λ posꟳ → ⟨ G.Pos ix posꟳ ⟩) (ua→⁻ p posꟳ))

    -- XXX: This is not the case.
    -- For example, when F.Param ix sꟳ = Bool, then (p q : SubstPos' sᴳ ≡ SubstPos' sᴳ)
    -- given by
    --  * p = id ⊎ id
    --  * q = swap ⊎ id
    -- are different paths.
    isProp-SubstPos' : ∀ s₀ s₁ → isProp (SubstPos' s₀ ≡ SubstPos' s₁)
    isProp-SubstPos' = ?

    SubstPos : (sᴳ : ⟨ SubstShapeᴰ sꟳ ⟩) → hSet _
    SubstPos = SQ.rec→Gpd.fun isGroupoidHSet SubstPos' SubstPos'-welldefined {! !}

  F[G]′ : ActCont.ob _
  F[G]′ .fst = SubstShape
  F[G]′ .snd (sꟳ , sᴳ) ix .fst = SubstSymm ix sꟳ sᴳ
  F[G]′ .snd (sꟳ , sᴳ) ix .snd .fst = {! !} -- F.Param ix sꟳ ⊎Set ΣSet (F.Free sꟳ) (G.Pos ix ∘ sᴳ)
  F[G]′ .snd (sꟳ , sᴳ) ix .snd .snd = {! !} -- F.action (just ix) sꟳ ⊎Action ΠActionΣ (F.Free sꟳ) (G.Pos ix ∘ sᴳ) (G.action ix ∘ sᴳ)
-}

module _ (F : ActCont[ Ix +1]) where
  private module F = ActCont+1₀ F

  {-
  subst-hom-class-fun : ∀ {G₀ G₁ : ActCont.ob Ix} → (φ : ActCont.hom Ix G₀ G₁) → ActCont.hom Ix (F [ G₀ ]-class-fun) (F [ G₁ ]-class-fun)
  subst-hom-class-fun {G₀} {G₁} φ@(φ₀ , φ₁) = F[g] where
    module G₀ = ActCont₀ G₀
    module G₁ = ActCont₀ G₁
    module φ = ActCont₁ φ
    module F[G₀] = ActCont₀ (F [ G₀ ]-class-fun)
    module F[G₁] = ActCont₀ (F [ G₁ ]-class-fun)

    shape-map : ⟨ F[G₀].Shape ⟩ → ⟨ F[G₁].Shape ⟩
    shape-map (sꟳ , sᴳ , class-fun) .fst = sꟳ
    shape-map (sꟳ , sᴳ , class-fun) .snd .fst = sᴳ ⋆ φ.shape-map
    shape-map (sꟳ , sᴳ , class-fun) .snd .snd p g = cong φ.shape-map (class-fun p g)

    module _ (ix : Ix) (sꟳ : ⟨ F.Shape ⟩) (sᴳ : ⟨ F.Pos free sꟳ ⟩ → ⟨ G₀.Shape ⟩) (class-fun : isClassFun (F.action free sꟳ) sᴳ) where
      private s* = (sꟳ , sᴳ , class-fun)

      symm-homᴰ : (pꟳ : ⟨ F.Free sꟳ ⟩) → GroupHom (G₀.Symm ix (sᴳ pꟳ)) (G₁.Symm ix (φ.shape-map (sᴳ pꟳ)))
      symm-homᴰ pꟳ = φ.symm-map ix (sᴳ pꟳ)

      symm-hom : GroupHom (F[G₀].Symm ix s*) (F[G₁].Symm ix (shape-map s*))
      symm-hom = mapSndHom {G = F.Symm (param ix) sꟳ} $ mapSndHom {G = F.Symm free sꟳ} $ mapΠGroup ℓ symm-homᴰ

      pos-map : ⟨ F[G₁].Pos ix (shape-map s*) ⟩ → ⟨ F[G₀].Pos ix s* ⟩
      pos-map = Sum.rec inl λ { (pꟳ , pos-G₁) → inr (pꟳ , φ.pos-map ix (sᴳ pꟳ) pos-G₁) }

      is-equivariant : isEquivariantMap[ symm-hom , pos-map ][ F[G₀].action ix s* , F[G₁].action ix (shape-map s*) ]
      is-equivariant (gꟳ-param , gꟳ-free , g₀) = funExt (Sum.elim (λ _ → refl) λ { (pos-free , pos-G₁) → cong inr (ΣPathP (refl , {! !})) })

    F[g] : ActCont.hom Ix (F [ G₀ ]-class-fun) (F [ G₁ ]-class-fun)
    F[g] .fst = shape-map
    F[g] .snd (sꟳ , sᴳ , class-fun) ix .fst = symm-hom ix sꟳ sᴳ class-fun
    F[g] .snd (sꟳ , sᴳ , class-fun) ix .snd .fst = pos-map ix sꟳ sᴳ class-fun
    F[g] .snd (sꟳ , sᴳ , class-fun) ix .snd .snd = is-equivariant ix sꟳ sᴳ class-fun
  -}

  subst-hom : ∀ {G₀ G₁ : ActCont.ob Ix} → (φ : ActCont.hom Ix G₀ G₁) → ActCont.hom Ix (F [ G₀ ]) (F [ G₁ ])
  subst-hom {G₀} {G₁} φ = F[g] where
    module G₀ = ActCont₀ G₀
    module G₁ = ActCont₀ G₁
    module φ = ActCont₁ φ
    module F[G₀] = ActCont₀ (F [ G₀ ])
    module F[G₁] = ActCont₀ (F [ G₁ ])

    shape-map : ⟨ F[G₀].Shape ⟩ → ⟨ F[G₁].Shape ⟩
    shape-map (sꟳ , sᴳ) .fst = sꟳ
    shape-map (sꟳ , sᴳ) .snd = sᴳ ⋆ φ.shape-map

    module _ (ix : Ix) (sꟳ : ⟨ F.Shape ⟩) (sᴳ : ⟨ F.Free/ sꟳ ⟩ → ⟨ G₀.Shape ⟩) where
      open Orbit (F.action free sꟳ) using ([_])
      private
        s* : ⟨ F[G₀].Shape ⟩
        s* = (sꟳ , sᴳ)

        sᴳ[_] : ⟨ F.Free sꟳ ⟩ → ⟨ G₀.Shape ⟩
        sᴳ[_] = sᴳ ∘ [_]

      symm-homᴰ : (y : ⟨ F.Free/ sꟳ ⟩) → GroupHom (G₀.Symm ix (sᴳ y)) (G₁.Symm ix (φ.shape-map (sᴳ y)))
      symm-homᴰ = φ.symm-map ix ∘ sᴳ

      symm-hom : GroupHom (F[G₀].Symm ix s*) (F[G₁].Symm ix (shape-map s*))
      symm-hom = mapSndHom {G = F.Symm (param ix) sꟳ} $ mapΠGroup ℓ symm-homᴰ

      pos-map : ⟨ F[G₁].Pos ix (shape-map s*) ⟩ → ⟨ F[G₀].Pos ix s* ⟩
      pos-map = Sum.rec inl λ { ([pꟳ] , pos-G₁) → inr ([pꟳ] , φ.pos-map ix (sᴳ [pꟳ]) pos-G₁) }

      is-equivariant : isEquivariantMap[ symm-hom , pos-map ][ F[G₀].action ix s* , F[G₁].action ix (shape-map s*) ]
      is-equivariant (gꟳ , g₀) = funExt λ where
        (Sum.inl pꟳ) → refl′ $ Sum.inl (gꟳ F.▷ pꟳ)
        (Sum.inr (pꟳ , pᴳ)) → cong inr (ΣPathP (refl , (φ.is-hom ix (sᴳ pꟳ) (g₀ pꟳ) ≡$ pᴳ)))

    F[g] : ActCont.hom Ix (F [ G₀ ]) (F [ G₁ ])
    F[g] .fst = shape-map
    F[g] .snd (sꟳ , sᴳ) ix .fst = symm-hom ix sꟳ sᴳ
    F[g] .snd (sꟳ , sᴳ) ix .snd .fst = pos-map ix sꟳ sᴳ
    F[g] .snd (sꟳ , sᴳ) ix .snd .snd = is-equivariant ix sꟳ sᴳ

  Subst : StrictFunctor (ActCont Ix) (ActCont Ix)
  Subst .StrictFunctor.F-ob = F [_]
  Subst .StrictFunctor.F-hom {x} {y} = subst-hom {x} {y}
  Subst .StrictFunctor.F-rel = trustme
  Subst .StrictFunctor.F-rel-id = trustme
  Subst .StrictFunctor.F-rel-trans = trustme
  Subst .StrictFunctor.F-hom-comp = trustme
  Subst .StrictFunctor.F-hom-id = trustme
  Subst .StrictFunctor.F-assoc-filler-left = trustme
  Subst .StrictFunctor.F-assoc-filler-right = trustme
  Subst .StrictFunctor.F-assoc = trustme
  Subst .StrictFunctor.F-unit-left-filler = trustme
  Subst .StrictFunctor.F-unit-left = trustme
  Subst .StrictFunctor.F-unit-right-filler = trustme
  Subst .StrictFunctor.F-unit-right = trustme
  -}
