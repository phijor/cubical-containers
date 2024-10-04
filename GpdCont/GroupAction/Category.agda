module GpdCont.GroupAction.Category where

open import GpdCont.Prelude
open import GpdCont.HomotopySet using (_→Set_)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Equivariant
open import GpdCont.DisplayedCategories using (Fam ; Famᴰ ; constᴰ)

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
