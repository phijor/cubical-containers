module GpdCont.GroupAction.Category where

open import GpdCont.Prelude
open import GpdCont.HomotopySet using (_→Set_)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Equivariant
open import GpdCont.DisplayedCategories using (Fam ; Famᴰ ; constᴰ)
open import GpdCont.Group.DeloopingCategory using (DeloopingCategory)
open import GpdCont.Group.MapConjugator using (Conjugatorsᴰ)

open import Cubical.Foundations.Equiv using (equiv→ ; _∙ₑ_ ; equivEq)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma as Sigma using (_×_)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom)

open import Cubical.Categories.Category.Base using (Category ; _^op ; _[_,_] ; seq')
open import Cubical.Categories.Functor.Base using (Functor)
open import Cubical.Categories.Instances.Groups using (GroupCategory)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Constructions.TotalCategory.Base using (∫C)
open import Cubical.Categories.Constructions.TotalCategory.Properties using (Fst)
open import Cubical.Categories.Constructions.BinProduct as Prod using (_×C_)
open import Cubical.Categories.Displayed.Base as Disp using (Categoryᴰ)
open import Cubical.Categories.Displayed.Constructions.Weaken.Base using (weaken)
open import Cubical.Categories.Displayed.Constructions.TotalCategory using (∫Cᴰ)
open import Cubical.Categories.Displayed.Constructions.Reindex.Base using (reindex)
open import Cubical.Categories.Displayed.Constructions.StructureOver using (StructureOver ; StructureOver→Catᴰ)
open import Cubical.Categories.Displayed.BinProduct using (_×ᴰ_)

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

module _ (ℓ : Level) where
  private
    Grpᵒᵖ : Category (ℓ-suc ℓ) ℓ
    Grpᵒᵖ = GroupCategory ^op

    variable
      G H K : Group ℓ
      X Y Z : hSet ℓ

  open Categoryᴰ
  open Action

  private
    Grp = GroupCategory {ℓ = ℓ}

    Setᵒᵖ : Category (ℓ-suc ℓ) ℓ
    Setᵒᵖ = SET ℓ ^op

    Grp×Setᵒᵖ : Category (ℓ-suc ℓ) ℓ
    Grp×Setᵒᵖ = Grp ×C Setᵒᵖ

  GroupActionBase : Category (ℓ-suc ℓ) ℓ
  GroupActionBase = Grp×Setᵒᵖ

  EquivariantMapStr : StructureOver (Grp ×C Setᵒᵖ) _ _
  EquivariantMapStr .StructureOver.ob[_] (G , X) = Action G X
  EquivariantMapStr .StructureOver.Hom[_][_,_] = isEquivariantMap[_][_,_]
  EquivariantMapStr .StructureOver.idᴰ {p = σ} = isEquivariantMap-id σ
  EquivariantMapStr .StructureOver._⋆ᴰ_ {f = φ×f} {g = ψ×p} {xᴰ = σ} {yᴰ = τ} {zᴰ = υ} = isEquivariantMap-comp φ×f ψ×p σ τ υ
  EquivariantMapStr .StructureOver.isPropHomᴰ {f = φ×f} {xᴰ = σ} {yᴰ = τ} = isPropIsEquivariantMap φ×f σ τ

  GroupActionᴰ : Categoryᴰ (Grp ×C Setᵒᵖ) ℓ ℓ
  GroupActionᴰ = StructureOver→Catᴰ EquivariantMapStr

  GroupAction : Category (ℓ-suc ℓ) ℓ
  GroupAction = ∫C GroupActionᴰ

mkGroupActionHom : ∀ {ℓ} {G H : Group ℓ} {X Y : hSet ℓ} {σ : Action G X} {τ : Action H Y}
  → (φ : GroupCategory [ G , H ])
  → (f : SET _ [ Y , X ])
  → isEquivariantMap[ φ , f ][ σ , τ ]
  → GroupAction ℓ [ ((G , X), σ) , ((H , Y) , τ) ]
mkGroupActionHom φ f is-eqva = λ where
  .fst .fst → φ
  .fst .snd → f
  .snd → is-eqva

GroupActionHom≡ : ∀ {ℓ} {G×X H×Y} → {f g : GroupAction ℓ [ G×X , H×Y ]} → f .fst ≡ g .fst → f ≡ g
GroupActionHom≡ {G×X} {H×Y} = Sigma.Σ≡Prop (λ φ×f → EquivariantMapStr _ .StructureOver.isPropHomᴰ {f = φ×f} {xᴰ = G×X .snd} {yᴰ = H×Y .snd})

private
  module GroupAction {ℓ} = Category (GroupAction ℓ)

module LocalCategory {ℓ} (σ*@((G , X) , σ) τ*@((H , Y), τ): GroupAction.ob {ℓ}) where
  private
    open module H = GroupStr (str H) using (_·_)
    module τ where
      open Action τ public
      open ActionProperties τ public

    Cell = GroupAction.Hom[ σ* , τ* ]
    variable
      φ ψ ρ : Cell

    cellData : (φ : Cell) → (⟨ G ⟩ → ⟨ H ⟩) × (⟨ Y ⟩ → ⟨ X ⟩)
    cellData (((φ , _) , f) , _) = φ , f

  homData = cellData

  hom→isGroupHom : (φ* : Cell) → (let (φ , _) = cellData φ*) → IsGroupHom (str G) φ (str H)
  hom→isGroupHom (((φ , φ-hom) , f) , _) = φ-hom

  -- H seen as a one-object category
  SymmCat : Category ℓ-zero _
  SymmCat = DeloopingCategory H

  isConjugator : (φ ψ : Cell) → ⟨ H ⟩ → Type _
  isConjugator φ* ψ* h
    using (φ , f) ← cellData φ*
    using (ψ , e) ← cellData ψ*
    = (∀ g → (φ g · h) ≡ (h · ψ g)) × (f ≡ e ∘ (τ ⁺ h))

  opaque
    isPropIsConjugator : (φ ψ : Cell) (h : ⟨ H ⟩) → isProp (isConjugator φ ψ h)
    isPropIsConjugator φ ψ h = isProp× (isPropΠ λ g → H.is-set _ _) (isSet→ (str X) _ _)

  opaque
    isConjugator-1g : isConjugator φ φ H.1g
    isConjugator-1g .fst g = H.·IdR _ ∙ sym (H.·IdL _)
    isConjugator-1g {φ} .snd using (_ , f) ← cellData φ = cong (f ∘_) $ sym τ.action-1-id

  opaque
    isConjugator-· : (φ ψ ρ : Cell) (h₁ h₂ : ⟨ H ⟩)
      → isConjugator φ ψ h₁
      → isConjugator ψ ρ h₂
      → isConjugator φ ρ (h₁ · h₂)
    isConjugator-· φ* ψ* ρ* h₁ h₂ (h-conj₁ , h-act₁) (h-conj₂ , h-act₂)
      using (φ , f) ← cellData φ*
      using (ψ , e) ← cellData ψ*
      using (ρ , d) ← cellData ρ*
      = goal where
      goal : isConjugator φ* ρ* (h₁ · h₂)
      goal .fst g =
        φ g · (h₁ · h₂) ≡⟨ H.·Assoc _ _ _ ⟩
        (φ g · h₁) · h₂ ≡⟨ cong (_· h₂) (h-conj₁ g) ⟩
        (h₁ · ψ g) · h₂ ≡⟨ sym $ H.·Assoc _ _ _ ⟩
        h₁ · (ψ g · h₂) ≡⟨ cong (h₁ ·_) (h-conj₂ g) ⟩
        h₁ · (h₂ · ρ g) ≡⟨ H.·Assoc _ _ _ ⟩
        (h₁ · h₂) · ρ g ∎
      goal .snd =
        f ≡⟨ h-act₁ ⟩
        e ∘ (τ ⁺ h₁) ≡⟨ cong (_∘ τ ⁺ h₁) h-act₂ ⟩
        d ∘ τ ⁺ h₂ ∘ τ ⁺ h₁ ≡⟨ cong (d ∘_) $ sym (τ.action-comp h₁ h₂) ⟩
        d ∘ τ ⁺ (h₁ · h₂) ∎

  -- The conjugation structure, displayed over H.
  -- A displayed object is an equivariant map, and displayed morphisms over some
  -- "conjugator" (h : H) are proofs that two equivariant maps are conjugate by `h`.
  ConjugatorStructure : StructureOver SymmCat _ _
  ConjugatorStructure .StructureOver.ob[_] = const GroupAction.Hom[ σ* , τ* ]
  ConjugatorStructure .StructureOver.Hom[_][_,_] h φ ψ = isConjugator φ ψ h
  ConjugatorStructure .StructureOver.idᴰ {p = φ} = isConjugator-1g {φ}
  ConjugatorStructure .StructureOver._⋆ᴰ_ {xᴰ = φ} {yᴰ = ψ} {zᴰ = ρ} = isConjugator-· φ ψ ρ _ _
  ConjugatorStructure .StructureOver.isPropHomᴰ {xᴰ = φ} {yᴰ = ψ} = isPropIsConjugator φ ψ _

  ConjugatorCat : Category ℓ ℓ
  ConjugatorCat = ∫C {C = SymmCat} (StructureOver→Catᴰ ConjugatorStructure)

  module ConjugatorCat = Category ConjugatorCat

  EquivariantConjugatorStr : StructureOver SymmCat _ _
  EquivariantConjugatorStr .StructureOver.ob[_] = const (⟨ Y ⟩ → ⟨ X ⟩)
  EquivariantConjugatorStr .StructureOver.Hom[_][_,_] h f₁ f₂ = f₁ ≡ f₂ ∘ (τ ⁺ h)
  EquivariantConjugatorStr .StructureOver.idᴰ {p = f} = cong (f ∘_) $ sym τ.action-1-id
  EquivariantConjugatorStr .StructureOver._⋆ᴰ_ {f = h} {g = h′} {xᴰ = f₁} {yᴰ = f₂} {zᴰ = f₃} f₁≡f₂∘τh f₂≡f₃∘τh′ =
    f₁ ≡⟨ f₁≡f₂∘τh ⟩
    f₂ ∘ (τ ⁺ h) ≡⟨ cong (_∘ τ ⁺ h) f₂≡f₃∘τh′ ⟩
    f₃ ∘ (τ ⁺ h′) ∘ (τ ⁺ h) ≡⟨ cong (f₃ ∘_) $ sym (τ.action-comp h h′) ⟩
    f₃ ∘ τ ⁺ (h · h′) ∎
  EquivariantConjugatorStr .StructureOver.isPropHomᴰ = isSet→ (str X) _ _

  EquivariantConjugatorᴰ : Categoryᴰ SymmCat _ _
  EquivariantConjugatorᴰ = StructureOver→Catᴰ EquivariantConjugatorStr

  ConjugatorCat' : Category ℓ ℓ
  ConjugatorCat' = ∫C {C = SymmCat} (Conjugatorsᴰ {G = G} {H} ×ᴰ EquivariantConjugatorᴰ)

  conjugator :  ∀ φ ψ → (h : ConjugatorCat.Hom[ φ , ψ ]) → ⟨ H ⟩
  conjugator _ _ = fst

  Conjugator≡ : ∀ {φ ψ} → (h₁ h₂ : ConjugatorCat.Hom[ φ , ψ ]) → conjugator φ ψ h₁ ≡ conjugator φ ψ h₂ → h₁ ≡ h₂
  Conjugator≡ {φ} {ψ} (h₁ , h₁-conj) (h₂ , h₂-conj) p = Sigma.ΣPathP
    (p , isProp→PathP (λ i → isPropIsConjugator (φ .snd) (ψ .snd) (p i)) h₁-conj h₂-conj)

{-
  Actᴰ : Categoryᴰ (GroupCategory {ℓ = ℓ}) (ℓ-suc ℓ) ℓ
  Actᴰ = ∫Cᴰ Grp×Setᵒᵖ GroupActionᴰ

  Act : Category (ℓ-suc ℓ) ℓ
  Act = Fam ℓ (∫C Actᴰ)

  test : Act .Category.ob ≡ (Σ[ S ∈ hSet _ ] (⟨ S ⟩ → Σ[ G ∈ Group _ ] Σ[ P ∈ hSet _ ] Action G P))
  test = refl

  SetContainer : Category (ℓ-suc ℓ) ℓ
  SetContainer = Fam ℓ (SET ℓ ^op)

  Shape : Functor SetContainer (SET ℓ)
  Shape = Fst

  ActionContainerStructure : Categoryᴰ SetContainer _ _
  ActionContainerStructure = ∫Cᴰ Symmᴰ Actionᴰ where
    FamGroupᴰ : Categoryᴰ (SET ℓ) (ℓ-suc ℓ) ℓ
    FamGroupᴰ = Famᴰ ℓ GroupCategory

    Symmᴰ : Categoryᴰ SetContainer (ℓ-suc ℓ) ℓ
    Symmᴰ = reindex FamGroupᴰ Shape

    FamActionᴰ : Categoryᴰ (SET ℓ) (ℓ-suc ℓ) ℓ
    FamActionᴰ = Famᴰ ℓ GroupAction

    Actionᴰ : Categoryᴰ (∫C Symmᴰ) (ℓ-suc ℓ) ℓ
    Actionᴰ = reindex FamActionᴰ {!Shape !}

  ActionContainerDisplayed : Category _ _
  ActionContainerDisplayed = ∫C {C = SetContainer} ActionContainerStructure

  module SetContainerSanity where
    open Category

    _ : SetContainer .ob ≡ (Σ[ S ∈ hSet ℓ ] (⟨ S ⟩ → hSet ℓ))
    _ = refl

    _ : ∀ {S T P Q} → (SetContainer [ (S , P) , (T , Q) ]) ≡ (Σ[ u ∈ SET _ [ S , T ] ] (∀ (s : ⟨ S ⟩) → ⟨ Q (u s) ⟩ → ⟨ P s ⟩))
    _ = refl

  -- ActionC : Category (ℓ-suc ℓ) ℓ
  -- ActionC = ∫C {C = SET ℓ} (∫Cᴰ Symm×ᴰPos Actionᴰ) where
  --   Symm : Categoryᴰ (SET ℓ) (ℓ-suc ℓ) ℓ
  --   Symm = Fam ℓ (GroupCategory {ℓ = ℓ})

  --   Pos : Categoryᴰ (SET ℓ) (ℓ-suc ℓ) ℓ
  --   Pos = Fam ℓ (SET ℓ ^op)

  --   Symm×ᴰPos : Categoryᴰ (SET ℓ) (ℓ-suc ℓ) ℓ
  --   Symm×ᴰPos = Symm ×ᴰ Pos
  
  --   Actionᴰ : Categoryᴰ (∫C Symm×ᴰPos) _ _
  --   ob[ Actionᴰ ] (S , (G , P)) = {! !}
  --   Actionᴰ .Hom[_][_,_] = {! !}
  --   Actionᴰ .idᴰ = {! !}
  --   Actionᴰ ._⋆ᴰ_ = {! !}
  --   Actionᴰ .⋆IdLᴰ = {! !}
  --   Actionᴰ .⋆IdRᴰ = {! !}
  --   Actionᴰ .⋆Assocᴰ = {! !}
  --   Actionᴰ .isSetHomᴰ = {! !}


  prf : (Act .Category.ob) ≃ ActionContainer ℓ
  prf =
    Act .Category.ob ≃⟨⟩
    (Σ[ S ∈ hSet ℓ ] (⟨ S ⟩ → Σ[ G ∈ Group ℓ ] Σ[ P ∈ hSet ℓ ] Action G P)) ≃⟨ snd-≃ (λ S → Σ-Π-≃) ⟩
    (Σ[ S ∈ hSet ℓ ] Σ[ G ∈ (⟨ S ⟩ → Group ℓ) ] ((s : ⟨ S ⟩) → Σ[ P ∈ hSet ℓ ] (Action (G s) P))) ≃⟨ snd-≃ (λ S → snd-≃ λ G → Σ-Π-≃) ⟩
    (Σ[ S ∈ hSet ℓ ] Σ[ G ∈ (⟨ S ⟩ → Group ℓ) ] (Σ[ P ∈ (⟨ S ⟩ → hSet ℓ) ] ∀ s → (Action (G s) (P s)))) ≃⟨ {! !} ⟩
    ActionContainer _ ≃∎

    where open Sigma using (Σ-Π-≃) renaming (Σ-cong-equiv-snd to snd-≃)
    -}
