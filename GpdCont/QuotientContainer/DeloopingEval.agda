{-# OPTIONS --lossy-unification #-}
module GpdCont.QuotientContainer.DeloopingEval where

open import GpdCont.Prelude hiding (Lift)
open import GpdCont.Equiv using (equivAdjointEquivExtDomain)
open import GpdCont.Univalence as UA using (ua ; ua→ ; ua→⁻)
open import GpdCont.HomotopySet using (_→Set_)
open import GpdCont.SetTruncation using (setTruncEquiv ; setTruncateFstΣ≃)
open import GpdCont.SetQuotients using (map ; relBiimpl→QuotIso)

open import GpdCont.QuotientContainer.Base using (QCont)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (preCompEquiv ; congEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
import      Cubical.Data.Sigma.Properties as Sigma
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.SetQuotients as SQ using (_/_)

-- Each endo-map on hGroupoids can be truncated to one on hSets.
Tr : ∀ {ℓ} (F : hGroupoid ℓ → hGroupoid ℓ) → (hSet ℓ → hSet ℓ)
Tr F (X , is-set-X) .fst = ∥ ⟨ F (X , isSet→isGroupoid is-set-X) ⟩ ∥₂
Tr F (X , is-set-X) .snd = ST.isSetSetTrunc

module _ {ℓ} (Q : QCont ℓ) where
  open import GpdCont.Polynomial using (Polynomial)
  import      GpdCont.Delooping as Delooping
  open import GpdCont.GroupAction.Base
  open import GpdCont.GroupAction.Pi using (preCompAction)
  open import GpdCont.GroupAction.AssociatedBundle using (associatedBundle ; _∼_ ; Orbits ; associatedBundleComponents≃Orbits)
  open import GpdCont.QuotientContainer.Delooping using () renaming (QContDelooping to 𝔹)
  open import GpdCont.QuotientContainer.Eval using (⟦_⟧-to-Σ ; LabelEquiv) renaming (⟦_⟧ to ⟦_⟧/ ; ⟦_⟧ᵗ to ⟦_⟧/ᵗ)
  open import GpdCont.SymmetricContainer.Base using (SymmetricContainer)
  open import GpdCont.SymmetricContainer.Eval using (⟦_⟧)

  private
    module Q = QCont Q
    module 𝔹Q = SymmetricContainer (𝔹 Q)

    𝔹Symm : (s : Q.Shape) → Type _
    𝔹Symm s = Delooping.𝔹 (Q.SymmGroup s)

    module 𝔹Symm {s} = Delooping (Q.SymmGroup s)

  LiftEvalEquiv : (X : hSet ℓ) → ⟨ Tr ⟦ 𝔹 Q ⟧ X ⟩ ≃ ⟨ ⟦ Q ⟧/ X ⟩
  LiftEvalEquiv X =
    ⟨ Tr ⟦ 𝔹 Q ⟧ X ⟩ ≃⟨⟩
    ∥ Polynomial 𝔹Q.Shape 𝔹Q.Pos ⟨ X ⟩ ∥₂ ≃⟨ setTruncEquiv (_ ≃Σ) ⟩
    ∥ Σ[ x ∈ Σ Q.Shape 𝔹Symm ] (𝔹Q.Pos x → ⟨ X ⟩) ∥₂                                          ≃⟨ setTruncEquiv Σ-assoc-≃ ⟩
    ∥ Σ[ s ∈ Q.Shape ] Σ[ x ∈ 𝔹Symm s ] (𝔹Q.Pos (s , x) → ⟨ X ⟩) ∥₂                           ≃⟨ setTruncateFstΣ≃ Q.is-set-shape ⟩
    Σ[ s ∈ Q.Shape ] ∥ Σ[ x ∈ 𝔹Symm s ] (𝔹Q.Pos (s , x) → ⟨ X ⟩) ∥₂                           ≃⟨⟩
    Σ[ s ∈ Q.Shape ] ∥ Σ[ x ∈ 𝔹Symm s ] (⟨ associatedBundle (Q.symmAction s) x ⟩ → ⟨ X ⟩) ∥₂  ≃⟨ Σ₂≃ assoc-bundle-equiv ⟩
    Σ[ s ∈ Q.Shape ] ∥ Σ[ x ∈ 𝔹Symm s ] (⟨ associatedBundle (σ* s) x ⟩) ∥₂                    ≃⟨ Σ₂≃ component-equiv ⟩
    Σ[ s ∈ Q.Shape ] Orbits (σ* s)                                                            ≃⟨ Σ₂≃ quotients-equiv ⟩
    Σ[ s ∈ Q.Shape ] ((Q.Pos s → ⟨ X ⟩) / LabelEquiv Q s ⟨ X ⟩)                               ≃⟨ invEquiv (⟦ Q ⟧-to-Σ .RecordToΣ.equivΣ) ⟩
    ⟦ Q ⟧/ᵗ ⟨ X ⟩ ≃∎
    where module _ (s : Q.Shape) where
      open Sigma using (Σ-assoc-≃) renaming (Σ-cong-equiv-snd to Σ₂≃) public

      σ = Q.symmAction

      σ* : Action (Q.SymmGroup s) (Q.PosSet s →Set X)
      σ* = preCompAction (σ s) X

      -- The connected components of the the total space of the bundle associated to σ*
      -- are exactly the σ*-orbits:
      component-equiv : ∥ Σ[ x ∈ 𝔹Symm s ] (⟨ associatedBundle σ* x ⟩) ∥₂ ≃ Orbits σ*
      component-equiv = associatedBundleComponents≃Orbits σ*

      assoc-bundle-fun : (x : 𝔹Symm s) → (⟨ associatedBundle (σ s) x ⟩ → ⟨ X ⟩) → ⟨ associatedBundle σ* x ⟩
      assoc-bundle-fun = 𝔹Symm.elimSet (λ x → isSet→ (str $ associatedBundle σ* x)) (id _) on-loops where
        on-loops : (g : Q.Symm s) → PathP
          (λ i → (ua (g .fst) i → ⟨ X ⟩) → ua (preCompEquiv {C = ⟨ X ⟩} (invEquiv (g .fst))) i)
          (id (Q.Pos s → ⟨ X ⟩))
          (id (Q.Pos s → ⟨ X ⟩))
        on-loops g = funExtNonDep pᴰ
          where module _ {q₀ q₁ : Q.Pos s → ⟨ X ⟩} (qᴰ : PathP (λ i → ua (g .fst) i → ⟨ X ⟩) q₀ q₁) where
          g* : (Q.Pos s → ⟨ X ⟩) ≃ (Q.Pos s → ⟨ X ⟩)
          g* = preCompEquiv (invEquiv $ g .fst)

          q : q₀ ≡ q₁ ∘ equivFun (g .fst)
          q = funExt (ua→⁻ qᴰ)

          p : q₀ ∘ invEq (g .fst) ≡ q₁
          p =
            q₀ ∘ invEq (g .fst) ≡[ i ]⟨ q i ∘ invEq (g .fst) ⟩
            q₁ ∘ equivFun (g .fst) ∘ invEq (g .fst) ≡[ i ]⟨ q₁ ∘ (λ x → secEq (g .fst) x i) ⟩
            q₁ ∎

          pᴰ : PathP (λ i → ua (preCompEquiv (invEquiv (g .fst))) i) q₀ q₁
          pᴰ = UA.ua-gluePath g* p

      -- The bundles associated to σ and σ* are related in the expected way:
      -- pointwise, the latter consists of sets of functions into X.
      assoc-bundle-equiv' : ∀ x → (⟨ associatedBundle (σ s) x ⟩ → ⟨ X ⟩) ≃ ⟨ associatedBundle σ* x ⟩
      assoc-bundle-equiv' x .fst = assoc-bundle-fun x
      assoc-bundle-equiv' x .snd = 𝔹Symm.elimProp (λ x → isPropIsEquiv $ assoc-bundle-fun x) (idIsEquiv _) x

      assoc-bundle-equiv : _ ≃ _
      assoc-bundle-equiv = setTruncEquiv $ Σ₂≃ assoc-bundle-equiv'

      -- The type of orbits of σ* and labels up to permutations are equivalent.
      -- In particular, both are set-quotients of the type `Q.Pos s → ⟨ X ⟩`.
      -- The relations `v ∼ w` (v and w are in the same orbit) and `LabelEquiv Q v w`
      -- (v and w are labels up to a permutation of their domain) are equivalent:
      rel-equiv : ∀ {v w} → _∼_ σ* v w ≃ LabelEquiv Q s ⟨ X ⟩ v w
      rel-equiv {v} {w} = PT.propTrunc≃ $ Σ₂≃ λ g → comm-equiv (g .fst) ∙ₑ ActionProperties.uaExtEquiv (σ s) g where
        comm-equiv : ∀ g → (v ∘ invEq g ≡ w) ≃ (v ≡ w ∘ equivFun g)
        comm-equiv g = equivAdjointEquivExtDomain g w v

      quotients-equiv : Orbits σ* ≃ ((Q.Pos s → ⟨ X ⟩) / LabelEquiv Q s ⟨ X ⟩)
      quotients-equiv = isoToEquiv $ relBiimpl→QuotIso idIso (equivFun rel-equiv) (invEq rel-equiv)
