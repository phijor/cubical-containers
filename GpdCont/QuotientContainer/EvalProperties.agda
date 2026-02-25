module GpdCont.QuotientContainer.EvalProperties where

open import GpdCont.Prelude
open import GpdCont.Equiv
open import GpdCont.Embedding using (Σ-map-snd ; Σ-map)
open import GpdCont.FinOrd
open import GpdCont.Univalence
open import GpdCont.QuotientContainer.CompositionOrdered
import      GpdCont.PropositionalTruncation as PT

import      GpdCont.SetQuotients as SQ
open import GpdCont.Group.Subgroup
open import GpdCont.Group.SymmetricGroup using (𝔖 ; symmConjGroupEquiv)
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Faithful

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_])
import      Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Binary.Base

QCont : Type₁
QCont = Σ[ S ∈ Type ] (isSet S) × (Σ[ P ∈ (S → FinOrd) ] Σ[ G ∈ (S → Group ℓ-zero) ] ∀ s → Action (G s) (FinOrd→hSet (P s)))

⟦_⟧ : QCont → Type → Type
⟦ S , is-set-S , P , G , σ ⟧ X = Σ[ s ∈ S ] ((⟨ P s ⟩ → X) / λ f f' → ∃[ g ∈ ⟨ G s ⟩ ] f ≡ f' ∘ (σ s ⁺ g))

module _
  (S T : Type)
  (is-set-S : isSet S)
  (is-set-T : isSet T)
  (P : S → FinOrd)
  (Q : T → FinOrd)
  (G : S → Group ℓ-zero)
  (σ : (s : S) → Action (G s) (FinOrd→hSet (P s)))
  (is-faithful-σ : ∀ s → isFaithful (σ s))
  (H : T → Group ℓ-zero)
  (τ : (t : T) → Action (H t) (FinOrd→hSet (Q t)))
  (is-faithful-τ : ∀ t → isFaithful (τ t))
  (perm-elim : (X : FinOrd) → SQ.Definable (Subgroup (𝔖 (FinOrd→hSet X)) ℓ-zero) _∼ˢᵘᵇ_)
  (inh-Q : ∀ {s} (p : ⟨ P s ⟩) → (f : ⟨ P s ⟩ → T) → ⟨ Q (f p) ⟩)
  where
  open Composition S T is-set-S is-set-T P Q G σ is-faithful-σ H τ is-faithful-τ perm-elim inh-Q

  isEquivRel-∼ : ∀ {s} → BinaryRelation.isEquivRel (_∼_ {s})
  isEquivRel-∼ = {! !}

  isProp-∼ : ∀ {s} → BinaryRelation.isPropValued (_∼_ {s})
  isProp-∼ f₀ f₁ = isProp∃ _ _

  isEffective-∼ : ∀ {s} → BinaryRelation.isEffective (_∼_ {s})
  isEffective-∼ = SQ.isEquivRel→isEffective isProp-∼ isEquivRel-∼

  private
    𝐅 : QCont
    𝐅 .fst = S
    𝐅 .snd .fst = is-set-S
    𝐅 .snd .snd .fst = P
    𝐅 .snd .snd .snd .fst = G
    𝐅 .snd .snd .snd .snd = σ

    𝐆 : QCont
    𝐆 .fst = T
    𝐆 .snd .fst = is-set-T
    𝐆 .snd .snd .fst = Q
    𝐆 .snd .snd .snd .fst = H
    𝐆 .snd .snd .snd .snd = τ

    𝐅𝐆 : QCont
    𝐅𝐆 .fst = Sh
    𝐅𝐆 .snd .fst = isSetSh
    𝐅𝐆 .snd .snd .fst = Ps
    𝐅𝐆 .snd .snd .snd .fst = Gr
    𝐅𝐆 .snd .snd .snd .snd = ac

  pres-comp-iso : (X : Type)
    → isSet X
    → Iso (⟦ 𝐅𝐆 ⟧ X) (⟦ 𝐅 ⟧ (⟦ 𝐆 ⟧ X))
  pres-comp-iso X is-set-X =
    Σ[ sh ∈ Sh ] (⟨ Ps sh ⟩ → X) / _
      Iso⟨ Σ-assoc-Iso ⟩
    (Σ[ s ∈ S ] Σ[ u ∈ _ ] (⟨ Ps (s , u) ⟩ → X) / _)
      Iso⟨ Σ-cong-iso-snd (λ s → SQ.setQuotientΣIso isEffective-∼ _ _ {! !}) ⟩
    Σ[ s ∈ S ] (Σ[ f ∈ (⟨ P s ⟩ → T) ] (⟨ Ps* s f ⟩ → X)) / _
      Iso⟨ Σ-cong-iso-snd (λ s → SQ.pullbackQuotIso (II s)) ⟩
    Σ[ s ∈ S ] (⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) / _
      Iso⟨ Σ-cong-iso-snd (λ s → SQ.relBiimpl→QuotIdIso {R = R₀ s} {S = R₁ s} {! !} {! (R₁→R₀ s) !}) ⟩
    Σ[ s ∈ S ] ((⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) / _)
      Iso⟨ Σ-cong-iso-snd (λ s → invIso (SQ.setQuotientMergeIso _ _ {! !})) ⟩
    Σ[ s ∈ S ] ((⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) / _) / _
      Iso⟨ Σ-cong-iso-snd III ⟩
    (Σ[ s ∈ S ] (⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X) / _) / _)
      Iso∎
      where module _ s where
        II : Iso
          (Σ[ f ∈ (⟨ P s ⟩ → T) ] (⟨ Ps* s f ⟩ → X))
          (⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X))
        II =
          (Σ[ f ∈ (⟨ P s ⟩ → T) ] (⟨ Ps* s f ⟩ → X))
            Iso⟨ Σ-cong-iso-snd (λ f → domIso $ equivToIso $ Ps*-Σ-equiv s f) ⟩
          (Σ[ f ∈ (⟨ P s ⟩ → T) ] ((Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩) → X))
            Iso⟨ Σ-cong-iso-snd (λ f → curryIso) ⟩
          (Σ[ f ∈ (⟨ P s ⟩ → T) ] ((p : ⟨ P s ⟩) → ⟨ Q (f p) ⟩ → X))
            Iso⟨ invIso Σ-Π-Iso ⟩
          (⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X))
            Iso∎

        fumble-inv : (⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) → (Σ[ f ∈ (⟨ P s ⟩ → T) ] (⟨ Ps* s f ⟩ → X))
        fumble-inv x .fst p = let f = x p .fst in f
        fumble-inv x .snd (t , (p , fp≡t) , q) = x p .snd $ subst (λ - → ⟨ Q - ⟩) (sym fp≡t) q

        fumble-β : II .Iso.inv ≡ fumble-inv
        fumble-β = refl

        inner : Iso
          (⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X) / _)
          ((⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) / _)
        inner =
          (⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X) / _)
            Iso⟨ codomainIso (SQ.setQuotientΣSndIso is-set-T (λ - → ⟨ Q - ⟩ → X) _) ⟩
          (⟨ P s ⟩ → (Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) / _)
            Iso⟨ invIso (setQuotientChoiceIso (P s) _ _) ⟩
          ((⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) / _)
            Iso∎

        inner-β : ∀ f → Iso.inv inner [ f ] ≡ (λ p → f p .fst , [ f p .snd ])
        inner-β f = refl

        III : Iso _ _
        III = invIso $ SQ.pullbackQuotIso inner

        II-β : ∀ f → Iso.inv II f ≡ ((λ p → f p .fst) , (λ (t , (p , fp≡t) , q) → f p .snd $ subst (λ - → ⟨ Q - ⟩) (sym fp≡t) q))
        II-β f = refl

        R₀ : _ → _ → Type _
        R₀ xx yy =
          let (f₀ , x₀) = Iso.inv II xx
              (f₁ , x₁) = Iso.inv II yy
          in
          Σ[ r ∈ f₀ ∼ f₁ ]
          Σ[ (x , _) ∈ (singlP (λ i → ⟨ Ps (s , SQ.eq/ _ _ r i) ⟩ → X) x₀) ]
          ∃[ g ∈ ⟨ Gr (s , [ f₁ ]) ⟩ ]
          x ≡ (x₁ ∘ (ac (s , [ f₁ ]) ⁺ g))

        opaque
          isProp-R₀ : ∀ f₀ f₁ → isProp (R₀ f₀ f₁)
          isProp-R₀ xx yy =
            let (f₀ , x₀) = Iso.inv II xx
                (f₁ , x₁) = Iso.inv II yy
            in
            isPropΣ (isProp-∼ f₀ f₁) λ r → isPropΣ (isContr→isProp (isContrSinglP _ _)) λ _ → isProp∃ _ _

        R₀′ : (fx₀ fx₁ : ⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) → Type _
        R₀′ _ _ = _

        R₀-equiv : ∀ (fx₀ fx₁ : ⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X))
          → R₀ fx₀ fx₁ ≃ R₀′ fx₀ fx₁
        R₀-equiv fx₀ fx₁
          using (f₀ , x₀) ← the (Σ[ f ∈ (⟨ P s ⟩ → T) ] (⟨ Ps* s f ⟩ → X)) $ Iso.inv II fx₀
          using (f₁ , x₁) ← the (Σ[ f ∈ (⟨ P s ⟩ → T) ] (⟨ Ps* s f ⟩ → X)) $ Iso.inv II fx₁
          =
            R₀ fx₀ fx₁
              ≃⟨ Σ-cong-equiv-snd (λ r → Σ-contractFst $ isContrSinglP _ x₀) ⟩
            Σ[ r ∈ f₀ ∼ f₁ ] ∃[ gr ∈ ⟨ Gr (s , [ f₁ ]) ⟩ ] subst (λ - → ⟨ Ps (s , -) ⟩ → X) (SQ.eq/ _ _ r) x₀ ≡ (x₁ ∘ (ac (s , [ f₁ ]) ⁺ gr))
              ≃⟨ {! !} ⟩
            Σ[ r ∈ f₀ ∼ f₁ ] ∃[ gr ∈ ⟨ Gr (s , [ f₁ ]) ⟩ ] PathP (λ i → ⟨ Ps (s , SQ.eq/ _ _ r i) ⟩ → X) x₀ (x₁ ∘ (ac (s , [ f₁ ]) ⁺ gr))
              ≃⟨ Σ-cong-equiv-snd (λ r → PT.propTrunc≃ $ Σ-cong-equiv (Gr-β≃ f₁) (λ gr → substEquiv (λ - → PathP (λ i → ⟨ Ps (s , SQ.eq/ _ _ r i) ⟩ → X) x₀ (x₁ ∘ -)) (ac-β f₁ gr))) ⟩
            Σ[ r ∈ f₀ ∼ f₁ ] ∃[ gr ∈ ⟨ Gr* s f₁ ⟩ ] PathP (λ i → ⟨ Ps (s , SQ.eq/ _ _ r i) ⟩ → X) x₀ (x₁ ∘ (ac* s f₁ ⁺ gr))
              ≃⟨ {! !} ⟩
            ∃[ r ∈ f₀ ≈ f₁ ] Σ[ gr ∈ ⟨ Gr* s f₁ ⟩ ] PathP (λ i → ⟨ Ps (s , SQ.eq/ _ _ PT.∣ r ∣₁ i) ⟩ → X) x₀ (x₁ ∘ (ac* s f₁ ⁺ gr))
              ≃⟨ {! !} ⟩
            ∃[ g ∈ ⟨ G s ⟩ ] Σ[ f₀∼f₁ ∈ f₀ ≡ f₁ ∘ (σ s ⁺ g) ] Σ[ gr ∈ ⟨ Gr* s f₁ ⟩ ] PathP (λ i → ⟨ Ps (s , SQ.eq/ _ _ PT.∣ g , f₀∼f₁ ∣₁ i) ⟩ → X) x₀ (x₁ ∘ (ac* s f₁ ⁺ gr))
              ≃⟨ {! !} ⟩
            ∃[ g ∈ ⟨ G s ⟩ ] Σ[ f₀∼f₁ ∈ f₀ ≡ f₁ ∘ (σ s ⁺ g) ] Σ[ h∣ ∈ ⟨ H∣ s f₁ ⟩ ] Σ[ g∣ ∈ ⟨ G∣ s f₁ ⟩ ] PathP (λ i → ⟨ Ps (s , SQ.eq/ _ _ PT.∣ g , f₀∼f₁ ∣₁ i) ⟩ → X) x₀ (x₁ ∘ (ac* s f₁ ⁺ (h∣ , g∣)))
              ≃⟨⟩
            ∃[ g ∈ ⟨ G s ⟩ ] Σ[ f₀∼f₁ ∈ f₀ ≡ f₁ ∘ (σ s ⁺ g) ] Σ[ h∣ ∈ (((t , _) : Σ T (fiber f₁)) → ⟨ H t ⟩) ] Σ[ g∣ ∈ ⟨ G∣ s f₁ ⟩ ] PathP (λ i → ⟨ Ps (s , SQ.eq/ _ _ PT.∣ g , f₀∼f₁ ∣₁ i) ⟩ → X) x₀ (x₁ ∘ (ac* s f₁ ⁺ (h∣ , g∣)))
              ≃⟨ {! !} ⟩
            ∃[ g ∈ ⟨ G s ⟩ ]
              Σ[ f₀∼f₁ ∈ f₀ ≡ f₁ ∘ (σ s ⁺ g) ]
              Σ[ h∣ ∈ (∀ p → ⟨ H (f₁ p) ⟩) ]
              Σ[ g∣ ∈ ⟨ G∣ s f₁ ⟩ ]
                PathP (λ i → ⟨ Ps (s , SQ.eq/ _ _ PT.∣ g , f₀∼f₁ ∣₁ i) ⟩ → X)
                  x₀
                  (x₁ ∘ (ac* s f₁ ⁺ ((λ (t , (p' , f₁p'≡t)) → subst (λ - → ⟨ H - ⟩) f₁p'≡t (h∣ p')) , g∣)))
              ≃∎

        {-
        R₀-equiv : ∀ (fx₀ fx₁ : ⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X))
          → R₀ fx₀ fx₁ ≃ R₀′ fx₀ fx₁
        R₀-equiv xx yy
          using (f₀ , x₀) ← Iso.inv II xx
          using (f₁ , x₁) ← Iso.inv II yy
          =
            R₀ xx yy
              ≃⟨ Σ-cong-equiv-snd (λ r → Σ-contractFst $ isContrSinglP _ x₀) ⟩
            Σ[ r ∈ f₀ ∼ f₁ ] ∃[ gr ∈ ⟨ Gr (s , [ f₁ ]) ⟩ ] subst (λ - → ⟨ Ps (s , -) ⟩ → X) (SQ.eq/ _ _ r) x₀ ≡ (x₁ ∘ (ac (s , [ f₁ ]) ⁺ gr))
              ≃⟨ invEquiv PT.propTruncΣ≃ ⟩
            ∃[ r ∈ f₀ ≈ f₁ ] Σ[ gr ∈ ⟨ Gr (s , [ f₁ ]) ⟩ ] subst (λ - → ⟨ Ps (s , -) ⟩ → X) (SQ.eq/ _ _ PT.∣ r ∣₁) x₀ ≡ (x₁ ∘ (ac (s , [ f₁ ]) ⁺ gr))
              ≃⟨ {! !} ⟩
            ∃[ g ∈ ⟨ G s ⟩ ] Σ[ f₀∼f₁ ∈ f₀ ≡ f₁ ∘ (σ s ⁺ g) ] Σ[ gr ∈ ⟨ Gr (s , [ f₁ ]) ⟩ ] subst (λ - → ⟨ Ps (s , -) ⟩ → X) (SQ.eq/ _ _ PT.∣ g , f₀∼f₁ ∣₁) x₀ ≡ (x₁ ∘ (ac (s , [ f₁ ]) ⁺ gr))
              ≃∎
        -}

        R₁ : _ → _ → Type _
        R₁ xx yy =
          let f₀ = Iso.inv inner [ xx ]
              f₁ = Iso.inv inner [ yy ]
          in ∃[ g ∈ ⟨ G s ⟩ ] f₀ ≡ f₁ ∘ (σ s ⁺ g)

        R₁′ : (f₀ f₁ : ⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) → Type _
        R₁′ _ _ = _

        R₁-equiv : (fx₀ fx₁ : ⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X))
          → R₁ fx₀ fx₁ ≃ R₁′ fx₀ fx₁
        R₁-equiv fx₀ fx₁
          using fx₀′ ← Iso.inv inner [ fx₀ ]
          using fx₁′ ← Iso.inv inner [ fx₁ ]
          using f₀ ← the (⟨ P s ⟩ → T) $ fst ∘ fx₀′
          using f₁ ← the (⟨ P s ⟩ → T) $ fst ∘ fx₁′
          using x₀ ← the ((p : ⟨ P s ⟩) → ⟨ Q (f₀ p) ⟩ → X) $ snd ∘ fx₀
          using x₁ ← the ((p : ⟨ P s ⟩) → ⟨ Q (f₁ p) ⟩ → X) $ snd ∘ fx₁
          =
            ∃[ g ∈ ⟨ G s ⟩ ] fx₀′ ≡ fx₁′ ∘ (σ s ⁺ g)
              ≃⟨ PT.propTrunc≃ (Σ-cong-equiv-snd λ g → invEquiv funExtEquiv) ⟩
            ∃[ g ∈ ⟨ G s ⟩ ] (∀ p → fx₀′ p ≡ fx₁′ (g σ.▷ p))
              ≃⟨ PT.propTrunc≃ (Σ-cong-equiv-snd λ g → equivΠCod λ p → invEquiv ΣPathP≃PathPΣ) ⟩
            ∃[ g ∈ ⟨ G s ⟩ ] (∀ p → Σ[ f₀∼f₁ ∈ f₀ p ≡ f₁ (g σ.▷ p) ] PathP (λ i → (⟨ Q (f₀∼f₁ i) ⟩ → X) / (λ f f' → ∃[ h ∈ ⟨ H (f₀∼f₁ i) ⟩ ] f ≡ f' ∘ (τ (f₀∼f₁ i) ⁺ h))) [ x₀ p ] [ x₁ (g σ.▷ p) ])
              ≃⟨ PT.propTrunc≃ (Σ-cong-equiv-snd λ g → equivΠCod λ p → Σ-cong-equiv-snd (λ p → PathP≃Path _ [ _ ] [ _ ])) ⟩
            ∃[ g ∈ ⟨ G s ⟩ ] (∀ p → Σ[ f₀∼f₁ ∈ f₀ p ≡ f₁ (g σ.▷ p) ] [ transport (λ i → ⟨ Q (f₀∼f₁ i) ⟩ → X) (x₀ p) ] ≡ [ x₁ (g σ.▷ p) ])
              ≃⟨ PT.propTrunc≃ (Σ-cong-equiv-snd λ g → equivΠCod λ p → Σ-cong-equiv-snd (λ p → invEquiv (SQ.eq/ _ _ , {! !}))) ⟩
            ∃[ g ∈ ⟨ G s ⟩ ] (∀ p → Σ[ f₀∼f₁ ∈ f₀ p ≡ f₁ (g σ.▷ p) ] ∃[ h ∈ ⟨ H (f₁ (g σ.▷ p)) ⟩ ] subst (λ - → ⟨ Q - ⟩ → X) f₀∼f₁ (x₀ p) ≡ x₁ (g σ.▷ p) ∘ τ (f₁ (g σ.▷ p)) ⁺ h)
              ≃⟨ {! PT.propTruncFstΣ≃ !} ⟩
            ∃[ g ∈ ⟨ G s ⟩ ] (∀ p → ∃[ f₀∼f₁ ∈ f₀ p ≡ f₁ (g σ.▷ p) ] Σ[ h ∈ ⟨ H (f₁ (g σ.▷ p)) ⟩ ] subst (λ - → ⟨ Q - ⟩ → X) f₀∼f₁ (x₀ p) ≡ x₁ (g σ.▷ p) ∘ τ (f₁ (g σ.▷ p)) ⁺ h)
              ≃⟨ {! !} ⟩ -- finite choice
            ∃[ g ∈ ⟨ G s ⟩ ] PT.∥ (∀ p → Σ[ f₀∼f₁ ∈ f₀ p ≡ f₁ (g σ.▷ p) ] Σ[ h ∈ ⟨ H (f₁ (g σ.▷ p)) ⟩ ] subst (λ - → ⟨ Q - ⟩ → X) f₀∼f₁ (x₀ p) ≡ x₁ (g σ.▷ p) ∘ τ (f₁ (g σ.▷ p)) ⁺ h) ∥₁
              ≃⟨ {! !} ⟩ -- idempotency of ∥_∥₁
            ∃[ g ∈ ⟨ G s ⟩ ] (∀ p → Σ[ f₀∼f₁ ∈ f₀ p ≡ f₁ (g σ.▷ p) ] Σ[ h ∈ ⟨ H (f₁ (g σ.▷ p)) ⟩ ] subst (λ - → ⟨ Q - ⟩ → X) f₀∼f₁ (x₀ p) ≡ x₁ (g σ.▷ p) ∘ τ (f₁ (g σ.▷ p)) ⁺ h)
              ≃⟨ {! !} ⟩
            ∃[ g ∈ ⟨ G s ⟩ ] Σ[ f₀∼f₁ ∈ f₀ ≡ f₁ ∘ (σ s ⁺ g) ] (∀ p → Σ[ h ∈ ⟨ H (f₁ (g σ.▷ p)) ⟩ ] subst (λ - → ⟨ Q - ⟩ → X) (f₀∼f₁ ≡$ p) (x₀ p) ≡ x₁ (g σ.▷ p) ∘ τ (f₁ (g σ.▷ p)) ⁺ h)
              ≃⟨ {! !} ⟩
            ∃[ g ∈ ⟨ G s ⟩ ] Σ[ f₀∼f₁ ∈ f₀ ≡ f₁ ∘ (σ s ⁺ g) ] (∀ p → Σ[ h ∈ ⟨ H (f₁ (g σ.▷ p)) ⟩ ] x₀ p ∘ subst (λ - → ⟨ Q - ⟩) (sym $ f₀∼f₁ ≡$ p) ≡ x₁ (g σ.▷ p) ∘ τ (f₁ (g σ.▷ p)) ⁺ h)
              ≃⟨ {! !} ⟩
            ∃[ g ∈ ⟨ G s ⟩ ] Σ[ f₀∼f₁ ∈ f₀ ≡ f₁ ∘ (σ s ⁺ g) ] (Σ[ h ∈ (∀ p → ⟨ H (f₁ (g σ.▷ p)) ⟩) ] ∀ p → x₀ p ∘ subst (λ - → ⟨ Q - ⟩) (sym $ f₀∼f₁ ≡$ p) ≡ x₁ (g σ.▷ p) ∘ τ (f₁ (g σ.▷ p)) ⁺ (h p))
              ≃∎

        opaque
          -- unfolding restrict-1g Ps*-well-defined
          unfolding Ps*-well-defined

          R₁′→R₀′-3 : ∀ fx₀ fx₁ → R₁′ fx₀ fx₁ → R₀′ fx₁ fx₀
          R₁′→R₀′-3 fx₀ fx₁
            using fx₀′ ← Iso.inv inner [ fx₀ ]
            using fx₁′ ← Iso.inv inner [ fx₁ ]
            using f₀ ← the (⟨ P s ⟩ → T) $ fst ∘ fx₀′
            using f₁ ← the (⟨ P s ⟩ → T) $ fst ∘ fx₁′
            using x₀ ← the ((p : ⟨ P s ⟩) → ⟨ Q (f₀ p) ⟩ → X) $ snd ∘ fx₀
            using x₁ ← the ((p : ⟨ P s ⟩) → ⟨ Q (f₁ p) ⟩ → X) $ snd ∘ fx₁
            = PT.map λ where
              (g , f₀∼f₁ , h , x-path) .fst → G.inv g
              (g , f₀∼f₁ , h , x-path) .snd .fst → {! !}
              (g , f₀∼f₁ , h , x-path) .snd .snd .fst p → subst (λ - → ⟨ H - ⟩) (sym (f₀∼f₁ ≡$ p)) (h p)
              (g , f₀∼f₁ , h , x-path) .snd .snd .snd .fst → G∣.1g s f₀
              (g , f₀∼f₁ , h , x-path) .snd .snd .snd .snd → {! !}

          R₁′→R₀′-2 : ∀ fx₀ fx₁ → R₁′ fx₀ fx₁ → R₀′ fx₀ fx₁
          R₁′→R₀′-2 fx₀ fx₁
            using fx₀′ ← Iso.inv inner [ fx₀ ]
            using fx₁′ ← Iso.inv inner [ fx₁ ]
            using f₀ ← the (⟨ P s ⟩ → T) $ fst ∘ fx₀′
            using f₁ ← the (⟨ P s ⟩ → T) $ fst ∘ fx₁′
            using x₀ ← the ((p : ⟨ P s ⟩) → ⟨ Q (f₀ p) ⟩ → X) $ snd ∘ fx₀
            using x₁ ← the ((p : ⟨ P s ⟩) → ⟨ Q (f₁ p) ⟩ → X) $ snd ∘ fx₁
            = PT.map λ where
              (g , f₀∼f₁ , h , x-path) .fst → g
              (g , f₀∼f₁ , h , x-path) .snd .fst → f₀∼f₁
              (g , f₀∼f₁ , h , x-path) .snd .snd .fst p → subst (λ - → ⟨ H (f₁ -) ⟩) (secEq (σ.action g) p) (h $ g σ.▷⁻ p)
              (g , f₀∼f₁ , h , x-path) .snd .snd .snd .fst → g , λ { t p → the ((f₁ p ≡ t) ≃ (f₁ (g σ.▷ p) ≡ t)) {! f₀∼f₁ !} }
              (g , f₀∼f₁ , h , x-path) .snd .snd .snd .snd → {! !}

          R₁′→R₀′ : ∀ fx₀ fx₁ → R₁′ fx₀ fx₁ → R₀′ fx₀ fx₁
          R₁′→R₀′ fx₀ fx₁
            using fx₀′ ← Iso.inv inner [ fx₀ ]
            using fx₁′ ← Iso.inv inner [ fx₁ ]
            using f₀ ← the (⟨ P s ⟩ → T) $ fst ∘ fx₀′
            using f₁ ← the (⟨ P s ⟩ → T) $ fst ∘ fx₁′
            using x₀ ← the ((p : ⟨ P s ⟩) → ⟨ Q (f₀ p) ⟩ → X) $ snd ∘ fx₀
            using x₁ ← the ((p : ⟨ P s ⟩) → ⟨ Q (f₁ p) ⟩ → X) $ snd ∘ fx₁
            = PT.map λ where
              (g , f₀∼f₁ , h , x-path) .fst → g
              (g , f₀∼f₁ , h , x-path) .snd .fst → f₀∼f₁
              (g , f₀∼f₁ , h , x-path) .snd .snd .fst p → subst (λ - → ⟨ H (f₁ -) ⟩) (secEq (σ.action g) p) (h $ g σ.▷⁻ p)
              (g , f₀∼f₁ , h , x-path) .snd .snd .snd .fst → G∣.1g s f₁
              (g , f₀∼f₁ , h , x-path) .snd .snd .snd .snd → ua→ λ where
                ps₀@(t , (p , f₀p≡t) , q) →
                  let
                    f₁gp≡t : f₁ (g σ.▷ p) ≡ t
                    f₁gp≡t = sym (f₀∼f₁ ≡$ p) ∙ f₀p≡t
                  in
                  x₀ p (transport (λ i → ⟨ Q (f₀p≡t (~ i)) ⟩) q)
                    ≡⟨ cong (x₀ p) {! !} ⟩
                  x₀ p (subst (λ - → ⟨ Q - ⟩) (sym (f₀∼f₁ ≡$ p)) (subst (λ - → ⟨ Q - ⟩) (sym $ (sym f₀∼f₁ ≡$ p) ∙ f₀p≡t) q))
                    ≡⟨ x-path p ≡$ transport (λ i → ⟨ Q (f₁gp≡t (~ i)) ⟩) q ⟩
                  x₁ (g σ.▷ p) (h p τ.▷ transport (λ i → ⟨ Q (f₁gp≡t (~ i)) ⟩) q)
                    ≡⟨ {! !} ⟩
                  x₁ (g σ.▷ p) (
                    subst (λ - → ⟨ Q - ⟩) (sym f₁gp≡t)
                      (transport (λ i → fst (H (f₁gp≡t i))) (h p) τ.▷ q)
                  )
                    ≡⟨ {!x₁ (G.1g σ.▷ (g σ.▷ p)) !} ⟩
                  x₁ (G.1g σ.▷ (g σ.▷ p)) (transport (λ i → fst (Q (restrict-1g s f₁ t (σ.action g .fst p) .fst f₁gp≡t (~ i))))
                    (
                      (transport (λ i → fst (H (f₁gp≡t i))) (h p)) τ.▷ q
                    )
                  )
                    -- cancel h(gg⁻p) ≡ h(p)
                    ≡⟨ {!x₁ (G.1g σ.▷ (g σ.▷ p)) !} ⟩
                  x₁ (G.1g σ.▷ (g σ.▷ p)) (transport (λ i → fst (Q (restrict-1g s f₁ t (σ.action g .fst p) .fst f₁gp≡t (~ i))))
                    (
                      (transport (λ i → fst (H (f₁gp≡t i)))
                        (transport (λ i → fst (H (f₁ (secEq (σ.action g) (g σ.▷ p) i)))) (h (g σ.▷⁻ (g σ.▷ p)))))
                      τ.▷
                      q
                    )
                  )
                    ∎

  {-
        R₁-refl : ∀ x → R₁ x x
        R₁-refl x = let f₁ = Iso.inv inner [ x ] in {! !}

        opaque
          R₁→R₀ : ∀ {x₀ x₁} → R₁ x₀ x₁ → R₀ x₀ x₁
          R₁→R₀ {x₀} {x₁} = ∃-rec (isProp-R₀ x₀ x₁) goal
            where module _ where
              f₀ = Iso.inv inner [ x₀ ]
              f₁ = Iso.inv inner [ x₁ ]

              module _ (g : ⟨ G s ⟩) (f₀≡f₁g : f₀ ≡ f₁ ∘ (σ s ⁺ g)) where
                -- restrict-g : Restrict s (fst ∘ f₁) g
                -- restrict-g t p = compPathlEquiv $ sym $ {! cong fst $ f₀≡f₁g ≡$ p!}

                goal : R₀ x₀ x₁
                goal .fst = ∃-intro g $ funExt λ p → cong fst $ f₀≡f₁g ≡$ p
                goal .snd .fst = ? -- _ , toPathP refl
                goal .snd .snd = ? -- ∃-intro (Gr-intro (Gr*.1g s (fst ∘ f₁))) $ funExt λ ps → {! !}
        -}
    
{-
  pres-comp : (X : Type)
    → isSet X
    → ⟦ 𝐅𝐆 ⟧ X ≃ ⟦ 𝐅 ⟧ (⟦ 𝐆 ⟧ X)
  pres-comp X is-set-X =
    Σ[ sh ∈ Sh ] (⟨ Ps sh ⟩ → X) / _
      ≃⟨ Σ-assoc-≃ ⟩
    Σ[ s ∈ S ] Σ[ u ∈ _ ] (⟨ Ps (s , u) ⟩ → X) / _
      ≃⟨ Σ-cong-equiv-snd (λ s → SQ.setQuotientΣ≃ isEffective-∼ _ _ {! !}) ⟩
    Σ[ s ∈ S ] (Σ[ f ∈ (⟨ P s ⟩ → T) ] (⟨ Ps* s f ⟩ → X)) / _
      ≃⟨ Σ-cong-equiv-snd (λ s → SQ.pullbackQuotEquiv (fumble s)) ⟩
    Σ[ s ∈ S ] (⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) / _
      ≃⟨ Σ-cong-equiv-snd (λ s → SQ.relBiimpl→QuotIdEquiv {R = R s} {! !} {! !}) ⟩
    Σ[ s ∈ S ] ((⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) / _)
      ≃⟨ Σ-cong-equiv-snd (λ s → invEquiv (SQ.setQuotientMerge≃ _ _ _)) ⟩
    Σ[ s ∈ S ] ((⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) / _) / _
      ≃⟨ Σ-cong-equiv-snd (λ s → invEquiv $ SQ.pullbackQuotEquiv $ isoToEquiv $ invIso $ setQuotientChoiceIso (P s) _ _) ⟩
    Σ[ s ∈ S ] (⟨ P s ⟩ → (Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) / _) / _
      ≃⟨ Σ-cong-equiv-snd (λ s → invEquiv $ SQ.pullbackQuotEquiv $ equivΠCod λ p → SQ.setQuotientΣSnd≃ is-set-T _ _) ⟩
    Σ[ s ∈ S ] (⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X) / _) / _
      ≃⟨⟩
    Σ[ s ∈ S ] (⟨ P s ⟩ → ⟦ 𝐆 ⟧ X) / _
      ≃∎
    where module _ s where
      fumble : (Σ[ f ∈ (⟨ P s ⟩ → T) ] (⟨ Ps* s f ⟩ → X)) ≃ (⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X))
      fumble =
        (Σ[ f ∈ (⟨ P s ⟩ → T) ] (⟨ Ps* s f ⟩ → X))
          ≃⟨ Σ-cong-equiv-snd (λ f → preCompEquiv $ invEquiv $ Ps*-Σ-equiv s f) ⟩
        (Σ[ f ∈ (⟨ P s ⟩ → T) ] ((Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩) → X))
          ≃⟨ Σ-cong-equiv-snd (λ f → curryEquiv) ⟩
        (Σ[ f ∈ (⟨ P s ⟩ → T) ] ((p : ⟨ P s ⟩) → ⟨ Q (f p) ⟩ → X))
          ≃⟨ invEquiv Σ-Π-≃ ⟩
        (⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X))
          ≃∎

      fumble-inv : (⟨ P s ⟩ → Σ[ t ∈ T ] (⟨ Q t ⟩ → X)) → (Σ[ f ∈ (⟨ P s ⟩ → T) ] (⟨ Ps* s f ⟩ → X))
      fumble-inv x .fst p = let f = x p .fst in f
      fumble-inv x .snd (t , (p , fp≡t) , q) = x p .snd $ subst (λ - → ⟨ Q - ⟩) (sym fp≡t) q

      fumble-β : invEq fumble ≡ fumble-inv
      fumble-β = refl

      R : _ → _ → Type _
      R xx yy =
        let (f₀ , x₀) = invEq fumble xx
            (f₁ , x₁) = invEq fumble yy
        in
        (Σ[ r ∈ (f₀ ∼ f₁) ] Σ[ (ps , _) ∈ (singlP (λ i → ⟨ Ps (s , SQ.eq/ f₀ f₁ r i) ⟩ → X) x₀) ] ∃[ g ∈ ⟨ Gr (s , [ f₁ ]) ⟩ ] ps ≡ x₁ ∘ ((ac (s , [ f₁ ]) ⁺ g)))

--       R' : _ → _ → Type _
--       R' xx yy = ∃[ g ∈ ⟨ G s ⟩ ]
--         (invEq (equivΠCod (λ p → SQ.setQuotientΣSnd≃ is-set-T (λ t → ⟨ Q t ⟩ → X) (λ v v₁ v₂ → ∃-syntax ⟨ H v ⟩ (λ g₁ → v₁ ≡ (λ x → v₂ ((τ v ⁺ g₁) x)))))) (invEq (isoToEquiv (invIso (setQuotientChoiceIso (P s) (Σ-syntax T (λ t → ⟨ Q t ⟩ → X)) (λ z z₁ → Σ (z .fst ≡ z₁ .fst) (λ p → Σ (Σ (fst (Q (z₁ .fst)) → X) (PathP (λ i → fst (Q (p i)) → X) (z .snd))) (λ .patternInTele0 → ∃-syntax ⟨ H (z₁ .fst) ⟩ (λ g₁ → .patternInTele0 .fst ≡ (λ x → z₁ .snd ((τ (z₁ .fst) ⁺ g₁) x))))))))) [ xx ]) ≡ (λ x → invEq (equivΠCod (λ p → SQ.setQuotientΣSnd≃ is-set-T (λ t → ⟨ Q t ⟩ → X) (λ v v₁ v₂ → ∃-syntax ⟨ H v ⟩ (λ g₁ → v₁ ≡ (λ x₁ → v₂ ((τ v ⁺ g₁) x₁)))))) (invEq (isoToEquiv (invIso (setQuotientChoiceIso (P s) (Σ-syntax T (λ t → ⟨ Q t ⟩ → X)) (λ z z₁ → Σ (z .fst ≡ z₁ .fst) (λ p → Σ (Σ (fst (Q (z₁ .fst)) → X) (PathP (λ i → fst (Q (p i)) → X) (z .snd))) (λ .patternInTele0 → ∃-syntax ⟨ H (z₁ .fst) ⟩ (λ g₁ → .patternInTele0 .fst ≡ (λ x₁ → z₁ .snd ((τ (z₁ .fst) ⁺ g₁) x₁))))))))) [ yy ]) ((σ s ⁺ g) x)))
-}
