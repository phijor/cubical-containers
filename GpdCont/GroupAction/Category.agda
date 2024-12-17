open import GpdCont.Prelude

module GpdCont.GroupAction.Category (ℓ : Level) where

open import GpdCont.HomotopySet using (_→Set_)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Equivariant
open import GpdCont.Categories.Family using (Fam ; Famᴰ)
open import GpdCont.Group.DeloopingCategory using (DeloopingCategory ; ∫DeloopingCategory)
open import GpdCont.Group.MapConjugator using (Conjugatorsᴰ ; ConjugatorStr)

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
open import Cubical.Categories.Displayed.HLevels using (hasPropHoms)
open import Cubical.Categories.Displayed.Constructions.Weaken.Base using (weaken)
open import Cubical.Categories.Displayed.Constructions.TotalCategory using (∫Cᴰ)
open import Cubical.Categories.Displayed.Constructions.Reindex.Base using (reindex)
open import Cubical.Categories.Displayed.Constructions.StructureOver using (StructureOver ; StructureOver→Catᴰ ; hasPropHomsStructureOver)
open import Cubical.Categories.Displayed.BinProduct using (_×ᴰ_)

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

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

mkGroupActionHom : ∀ {G H : Group ℓ} {X Y : hSet ℓ} {σ : Action G X} {τ : Action H Y}
  → (φ : GroupCategory [ G , H ])
  → (f : SET _ [ Y , X ])
  → isEquivariantMap[ φ , f ][ σ , τ ]
  → GroupAction [ ((G , X), σ) , ((H , Y) , τ) ]
mkGroupActionHom φ f is-eqva = λ where
  .fst .fst → φ
  .fst .snd → f
  .snd → is-eqva

GroupActionHom≡ : ∀ {G×X H×Y} → {f g : GroupAction [ G×X , H×Y ]} → f .fst ≡ g .fst → f ≡ g
GroupActionHom≡ {G×X} {H×Y} = Sigma.Σ≡Prop (λ φ×f → EquivariantMapStr .StructureOver.isPropHomᴰ {f = φ×f} {xᴰ = G×X .snd} {yᴰ = H×Y .snd})

private
  module GroupAction = Category GroupAction

module LocalCategory (σ*@((G , X) , σ) τ*@((H , Y), τ): GroupAction.ob) where
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

  EquivariantConjugatorsᴰ : Categoryᴰ SymmCat _ _
  EquivariantConjugatorsᴰ = StructureOver→Catᴰ EquivariantConjugatorStr

  ConjugatorCatᴰ : Categoryᴰ SymmCat _ _
  ConjugatorCatᴰ = Conjugatorsᴰ {G = G} {H} ×ᴰ EquivariantConjugatorsᴰ

  hasPropHomsConjugatorCatᴰ : hasPropHoms ConjugatorCatᴰ
  hasPropHomsConjugatorCatᴰ h (φ , f) (ψ , g) = isProp×
    (hasPropHomsStructureOver ConjugatorStr h φ ψ)
    (hasPropHomsStructureOver EquivariantConjugatorStr h f g)

  ConjugatorCat : Category ℓ ℓ
  ConjugatorCat = ∫DeloopingCategory H ConjugatorCatᴰ

  module ConjugatorCat = Category ConjugatorCat

  conjugator :  ∀ φ ψ → (h : ConjugatorCat.Hom[ φ , ψ ]) → ⟨ H ⟩
  conjugator _ _ = fst

  Conjugator≡ : ∀ {φ ψ} → (h₁ h₂ : ConjugatorCat.Hom[ φ , ψ ]) → conjugator φ ψ h₁ ≡ conjugator φ ψ h₂ → h₁ ≡ h₂
  Conjugator≡ {φ} {ψ} (h₁ , h₁-conj) (h₂ , h₂-conj) p = Sigma.ΣPathP
    (p , isProp→PathP (λ i → hasPropHomsConjugatorCatᴰ (p i) φ ψ) h₁-conj h₂-conj)
