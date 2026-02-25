open import GpdCont.Prelude

module GpdCont.Analytic.Base (ℓ : Level) where

open import GpdCont.HomotopySet
open import GpdCont.Univalence
open import GpdCont.Axioms.TruncatedChoice using (ASC)
open import GpdCont.Categories.Family
open import GpdCont.Group.DirProd
open import GpdCont.Group.WreathProduct
open import GpdCont.Group.SymmetricGroup using (𝔖)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Category ℓ
open import GpdCont.GroupAction.Stabilizer using (module Setwise ; isPropIsStabilizer)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset as ℙ using (ℙ)
import      Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.PropositionalTruncation.Monad using (_>>=_ ; return)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Pi
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.EssentialImage
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors.Endo

Endo : Category (ℓ-suc ℓ) (ℓ-suc ℓ)
Endo = EndofunctorCategory (SET ℓ)

Cont : Category (ℓ-suc ℓ) ℓ
Cont = Fam ℓ GroupAction

private
  module Endo = Category Endo
  module GroupAction = Category GroupAction

  module Cont where
    open Category Cont public

    module ₀ (F@(S , σ) : ob) where
      Sym : ⟨ S ⟩ → Group ℓ
      Sym s = σ s .fst .fst

      Pos : ⟨ S ⟩ → hSet ℓ
      Pos s = σ s .fst .snd

      Act : (s : ⟨ S ⟩) → Action (Sym s) (Pos s)
      Act s = σ s .snd

      module Act {s} = Action (Act s)

      FunEquiv : (X : Type ℓ) → ∀ {s} → (f₀ f₁ : ⟨ Pos s ⟩ → X) → Type _
      FunEquiv X {s} f₀ f₁ = ∃[ g ∈ ⟨ Sym s ⟩ ] PathP (λ i → ua (Act.action g) i → X) f₀ f₁

⟦-⟧ᵃ : Functor GroupAction Endo
⟦-⟧ᵃ = {! !} where
  ⟦-⟧₀ : GroupAction.ob → Endo.ob
  ⟦-⟧₀ ((G , X) , σ) = {! !}

⟦_⟧ : Cont.ob → Endo.ob
⟦ (S , σ) ⟧ = {! !} where
  ⟦-⟧₀ : hSet ℓ → hSet ℓ
  ⟦-⟧₀ X = ΣSet S λ s → (⟦-⟧ᵃ ⟅ σ s ⟆) ⟅ X ⟆

⟦-⟧ : Functor Cont Endo
⟦-⟧ = {! !}

isAnalytic : (F : Endo.ob) → Type _
-- isAnalytic F = ∃[ C ∈ Cont.ob ] ⟦ C ⟧ ≅ᶜ F
isAnalytic = isInEssentialImage ⟦-⟧

Ana : Category (ℓ-suc ℓ) (ℓ-suc ℓ)
Ana = EssentialImage ⟦-⟧

module _ (ac : ASC ℓ (ℓ-suc ℓ)) where
  cont-comp : (Fᵒ Fⁱ : Cont.ob) → ∥ Cont.ob ∥₁
  cont-comp Fᵒ@(S , _) Fⁱ@(T , _) = goal where
    open module Fᵒ = Cont.₀ Fᵒ
      using ()
      renaming (Sym to G ; Pos to P ; Act to σ ; module Act to σ)
    open module Fⁱ = Cont.₀ Fⁱ
      using ()
      renaming (Sym to H ; Pos to Q ; Act to τ)

    _∼_ = Fᵒ.FunEquiv ⟨ T ⟩

    U : hSet ℓ
    U = ΣSet S λ s → (⟨ P s ⟩ → ⟨ T ⟩) / _∼_ , SQ.squash/

    module _ {s} (f : ⟨ P s ⟩ → ⟨ T ⟩) where
      R* : hSet ℓ
      R* = ΣSet (P s) (Q ∘ f)

      module Stab where
        open Setwise (G s) (P s) (σ s) public

      Fix : ⟨ T ⟩ → ℙ ⟨ P s ⟩
      Fix t p .fst = f p Eq.≡ t
      Fix t p .snd = {! !} -- str T _ _

      K*-inner : ⟨ T ⟩ → Group ℓ
      K*-inner t = Stab.StabilizerGroup' (Fix t)

      K* : Group ℓ
      K* = ΠGroup λ (t : ⟨ T ⟩) → Wreath _ (H t) (K*-inner t) (Stab.SubsetAction' (Fix t))

      υ→ : ⟨ K* ⟩ → ⟨ 𝔖 R* ⟩
      υ→ k .fst (p , q) =
        let (h-fib , g , stab-g) = k (f p)
            h = h-fib (p , Eq.refl)
            adj : f p Eq.≡ f (g σ.▷ p)
            adj = Eq.sym (stab-g p .snd (Eq.refl))
        in (g σ.▷ p) , Eq.transport (⟨_⟩ ∘ Q) adj (h τ.▷ q)
      υ→ k .snd = {! !}

      υ*ᴰ : Action K* R*
      υ*ᴰ .Action.action = υ→
      υ*ᴰ .Action.pres· k k' = {! !}

      υ* : GroupAction.ob
      υ* = (K* , R*) , υ*ᴰ

    module _ {s} (f₀ f₁ : ⟨ P s ⟩ → ⟨ T ⟩) where
      R*-well-defined : f₀ ∼ f₁ → ST.∣ R* f₀ ∣₂ ≡ ST.∣ R* f₁ ∣₂
      R*-well-defined = ∃-rec (ST.isSetSetTrunc _ _) λ g p → cong ST.∣_∣₂ $ hSet≡ $ Σ-cong' (ua $ σ.action g) λ i x → ⟨ Q (p i x) ⟩

    ∣R∣ : ⟨ U ⟩ → ∥ hSet ℓ ∥₂
    ∣R∣ = uncurry λ s → SQ.rec ST.isSetSetTrunc (ST.∣_∣₂ ∘ R*) R*-well-defined

    υ : ⟨ U ⟩ → ∥ GroupAction.ob ∥₁
    υ = uncurry λ s → SQ.elimProp (λ _ → PT.isPropPropTrunc) (PT.∣_∣₁ ∘ υ*)

    υ' : ⟨ U ⟩ → ∥ GroupAction.ob ∥₂
    υ' = uncurry λ s → SQ.elim (λ _ → ST.isSetSetTrunc) (ST.∣_∣₂ ∘ υ*) {! !}

    goal : ∥ Cont.ob ∥₁
    goal = do
      υ* ← ac U (λ _ → GroupAction.ob , {! !}) {! !}
      return (U , υ*)

  anaComp : (F G : Endo.ob) → isAnalytic F → isAnalytic G → isAnalytic (F ∘F G)
  anaComp F G ana-F ana-G = do
    (⟦F⟧ , α) ← ana-F
    (⟦G⟧ , β) ← ana-G
    ⟦F∘G⟧ ← cont-comp ⟦F⟧ ⟦G⟧
    return (⟦F∘G⟧ , {! !})
