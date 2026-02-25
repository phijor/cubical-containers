module GpdCont.QuotientContainer.CompositionOrdered where

open import GpdCont.Prelude
open import GpdCont.Prelude.Path
open import GpdCont.Prelude.Square
open import GpdCont.FinOrd
open import GpdCont.Equiv
open import GpdCont.Embedding
open import GpdCont.Univalence
open import GpdCont.HomotopySet
import      GpdCont.SetQuotients as SQ
import      GpdCont.Subuniverse
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Pi
open import GpdCont.GroupAction.Stabilizer using (module Setwise ; isPropIsStabilizer)
open import GpdCont.GroupAction.Equivariant
open import GpdCont.GroupAction.Faithful
open import GpdCont.Group.SymmetricGroup using (𝔖 ; symmConjGroupEquiv)
open import GpdCont.Group.Subgroup
open import GpdCont.Group.DirProd
open import GpdCont.Group.Pi using (ΠGroupEquiv)
open import GpdCont.Group.Opposite
open import GpdCont.Group.SemidirectProduct
open import GpdCont.Group.WreathProduct
open import GpdCont.Group.Equivs using (conjEquiv ; conjGroupEquiv)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset as ℙ using (ℙ)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Foundations.Path as Path using (compPathlEquiv ; congPathIso ; isProp→isPropPathP)
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic as Logic using (hProp≡)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Functions.Fibration
import      Cubical.Data.Empty as Empty
import      Cubical.Data.Fin.Recursive as FinR
open import Cubical.Data.FinSet as FinSet using (isFinOrd)
import      Cubical.Data.FinSet.Constructors as FinSet
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.SumFin as Fin using (totalSum)
open import Cubical.Data.Unit
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Pi
open import Cubical.Algebra.Group.GroupPath using (isGroupoidGroup ; uaGroup)
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_])
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)

{-# INJECTIVE_FOR_INFERENCE ⟨_⟩ #-}

open Subgroup

_∼ˢᵘᵇ_ : {G : Group ℓ-zero} → (H₀ H₁ : Subgroup G ℓ-zero) → Type _
H₀ ∼ˢᵘᵇ H₁ = GroupEquiv (H₀ .sub) (H₁ .sub)
{-# INJECTIVE_FOR_INFERENCE _∼ˢᵘᵇ_ #-}

Subgroup/ : (G : Group ℓ-zero) → Type _
Subgroup/ G = (Subgroup G ℓ-zero) / _∼ˢᵘᵇ_

private
  totalIso : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
    → (f : X → Y)
    → Iso X (Σ[ y ∈ Y ] (fiber f y))
  totalIso f .Iso.fun x .fst = f x
  totalIso f .Iso.fun x .snd .fst = x
  totalIso f .Iso.fun x .snd .snd = refl
  totalIso f .Iso.inv (y , x , fx≡y) = x
  totalIso f .Iso.rightInv (y , x , fx≡y) i .fst = fx≡y i
  totalIso f .Iso.rightInv (y , x , fx≡y) i .snd .fst = x
  totalIso f .Iso.rightInv (y , x , fx≡y) i .snd .snd j = fx≡y (i ∧ j)
  totalIso f .Iso.leftInv _ = refl

module Composition
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

  module perm-elim X = SQ.Definable (perm-elim X)

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

  Sh : Type _
  Sh = Σ[ s ∈ S ] ((⟨ P s ⟩ → T) / _∼_)

  isSetSh : isSet Sh
  isSetSh = isSetΣ is-set-S λ s → SQ.squash/

  module _ (s : S) (f : ⟨ P s ⟩ → T) where
    Ps*-contr-equiv : (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩) ≃ (Σ[ t ∈ T ] (fiber f t) × ⟨ Q t ⟩)
    Ps*-contr-equiv =
      Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩
        ≃⟨ Σ-cong-equiv-fst (totalEquiv f) ⟩
      Σ[ (t , _) ∈ Σ T (fiber f) ] ⟨ Q t ⟩
        ≃⟨ Σ-assoc-≃ ⟩
      Σ[ t ∈ T ] (fiber f t) × ⟨ Q t ⟩
        ≃∎

    Ps* : FinOrd
    Ps* .fst = Σ[ t ∈ T ] (fiber f t) × ⟨ Q t ⟩
    Ps* .snd = isFinOrdRespectEquiv (invEquiv Ps*-contr-equiv) (str $ FinOrdΣ (P s) (Q ∘ f))

    Ps*-Σ-Iso : Iso (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩) ⟨ Ps* ⟩
    Ps*-Σ-Iso =
      (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩)
        Iso⟨ Σ-cong-iso-fst (totalIso f) ⟩
      Σ[ (t , _) ∈ Σ T (fiber f) ] ⟨ Q t ⟩
        Iso⟨ Σ-assoc-Iso ⟩
      Σ[ t ∈ T ] (fiber f t) × ⟨ Q t ⟩
        Iso∎

    Ps*-Σ-equiv : ⟨ Ps* ⟩ ≃ (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩)
    Ps*-Σ-equiv = invEquiv $
      (Σ[ p ∈ ⟨ P s ⟩ ] ⟨ Q (f p) ⟩)
        ≃⟨ Σ-cong-equiv-fst (totalEquiv f) ⟩
      Σ[ (t , _) ∈ Σ T (fiber f) ] ⟨ Q t ⟩
        ≃⟨ Σ-assoc-≃ ⟩
      Σ[ t ∈ T ] (fiber f t) × ⟨ Q t ⟩
        ≃∎

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
    G∣ = G∣≤ .sub

    module G∣ = GroupStr (str G∣)

    Fiber : T → hSet _
    Fiber t .fst = fiber f t
    Fiber t .snd = isSetΣSndProp (str $ FinOrd→hSet (P s)) λ p → is-set-T (f p) t

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

    module Gr* = GroupStr (str Gr*)

    ac* : Action Gr* (FinOrd→hSet Ps*)
    ac* .Action.action (h , g∣) = equiv where
      equiv : ⟨ 𝔖 (FinOrd→hSet Ps*) ⟩
      equiv = Σ-cong-equiv-snd λ t → Σ-cong-equiv (σ∣.action {t} g∣) λ fib → (τ.action (h (t , fib)))
    ac* .Action.pres· (h₀ , g∣₀) (h₁ , g∣₁) = equivEq $ funExt λ where
      (t , fib , q) → ΣPathP λ where
        .fst → refl′ t
        .snd → ΣPathP λ where
          .fst → σ∣.action-comp-ext g∣₀ g∣₁ fib
          .snd → τ.action-comp-ext (h₀ (t , fib)) (h₁ (t , g∣₀ σ∣.▷ fib)) q

    module ac* = Action ac*

    -- XXX: This depends on inh-Q
    isFaithful-ac* : isFaithful ac*
    isFaithful-ac* {g = h₀ , g∣₀} {h = h₁ , g∣₁} htpy = ΣPathP λ where
      .fst → funExt λ where
        (t , fib) → is-faithful-τ t $ equivExt λ where
          q → rectify {A = T} {B = λ t → ⟨ Q t ⟩} is-set-T (cong (snd ∘ snd) $ funExt⁻ (cong equivFun htpy) (t , fib , q))
      .snd → Σ≡Prop isPropRestrict $ is-faithful-σ s $ equivExt λ p → cong (fst ∘ fst ∘ snd) (funExt⁻ (cong equivFun htpy) (f p , (p , refl) , inh-Q p f))

    GrSub* : Subgroup (𝔖 (FinOrd→hSet Ps*)) ℓ-zero
    GrSub* .sub = Gr*
    GrSub* .is-sub = isFaithful→isSubgroup {σ = ac*} $ isFaithful-ac*

  {-
  λ where
    g eq → ΣPathP λ where
      .fst → ua $ Σ-cong-equiv-snd λ t → Σ-cong-equiv-fst (Σ-cong-equiv (σ.action g) (λ p → compPathlEquiv (sym (eq ≡$ p))))
      .snd → ΣPathP λ where
        .fst →
          let α = str (P s) .snd
          in Fin-inj $ totalSum-permute-snd _ _ (invEquiv α ∙ₑ σ.action g ∙ₑ α) $ funExt
            λ p → cong (card ∘ Q) $
              let α = str (P s) .snd in
              f (invEq α p)
                ≡⟨ eq ≡$ (invEq α p) ⟩
              f' (g σ.▷ (invEq α p))
                ≡[ i ]⟨ f' (retEq α (g σ.▷ invEq α p) (~ i) ) ⟩
              f' (invEq α (equivFun α (g σ.▷ (invEq α p))))
                ∎
        -- .snd → equivPathP $ Iso.fun (congPathIso {A = λ i → {! str (P s) !}} {B = λ i → ua (Σ-cong-equiv-snd (λ t → Σ-cong-equiv-fst (Σ-cong-equiv (σ.action g) (λ p → compPathlEquiv (λ i₁ → (eq ≡$ p) (~ i₁)))))) i → Fin.Fin (Fin-inj (totalSum-permute-snd (λ x → card (Q (f (invEq (str (P s) .snd) x)))) (λ v → str (Q (f' (invEq (Cubical.Data.FinSet.Constructors.e ⟨ P s ⟩ (snd (P s)) (λ x → ⟨ Q (f' x) ⟩) (λ x → str (Q (f' x)))) v))) .fst) (invEquiv (str (P s) .snd) ∙ₑ σ.action g ∙ₑ str (P s) .snd) (funExt (λ p i₁ → card (Q (step-≡ (f (invEq (str (P s) .snd) p)) (≡⟨⟩-syntax (f' ((σ s Action.▷ g) (invEq (str (P s) .snd) p))) (f' (invEq (str (P s) .snd) (equivFun (str (P s) .snd) ((σ s Action.▷ g) (invEq (str (P s) .snd) p)))) ∎) (λ i₂ → f' (retEq (str (P s) .snd) ((σ s Action.▷ g) (invEq (str (P s) .snd) p)) (~ i₂)))) (eq ≡$ invEq (str (P s) .snd) p) i₁))))) i)} (λ i → {! !})) {! !} -- ua→ λ ps → toPathP {! !}
        .snd → equivPathP $ ua→ λ ps → toPathP {! !}
        -}

  -- TODO: Switch back to this later
  module _ s (f f' : ⟨ P s ⟩ → T) where opaque
    Ps*-well-defined : f ∼ f' → Ps* s f ≡ Ps* s f'
    Ps*-well-defined = ∃-rec (isSetFinOrd _ _) goal where
      module _ (g : ⟨ G s ⟩) (f∼f' : f ≡ f' ∘ (σ s ⁺ g)) where
        π : ⟨ P s ⟩ ≃ ⟨ Fin (card (P s)) ⟩
        π = str (P s) .snd

        ρ : (Σ[ t ∈ T ] (fiber f t) × ⟨ Q t ⟩) ≃ (Σ[ t ∈ T ] (fiber f' t) × ⟨ Q t ⟩)
        ρ = Σ-cong-equiv-snd λ t → Σ-cong-equiv-fst (Σ-cong-equiv (σ.action g) (λ p → compPathlEquiv (sym (f∼f' ≡$ p))))

        ρ' : (Σ[ t ∈ T ] (fiber f t) × ⟨ Q t ⟩) ≃ (Σ[ t ∈ T ] (fiber f' t) × ⟨ Q t ⟩)
        ρ' = Σ-cong-equiv-snd λ t → Σ-cong-equiv-fst ((λ { (p , fp≡t) → (σ s ⁺ g) p , sym (f∼f' ≡$ p) ∙ fp≡t }) , {! !})

        card-path : totalSum (card ∘ Q ∘ f ∘ invEq π) ≡ totalSum (card ∘ Q ∘ f' ∘ invEq π)
        card-path = {! totalSum-permute-snd !}

        module _ (t : T) (p : ⟨ P s ⟩) (fp≡t : f p ≡ t) (q : ⟨ Q t ⟩) where
          to-fin-path-ext :
            PathP (λ i → ⟨ Fin (card-path i) ⟩)
              (equivFun (to-fin (Ps* s f)) (t , (p , fp≡t) , q))
              (equivFun (to-fin (Ps* s f')) $ equivFun ρ (t , (p , fp≡t) , q))
          to-fin-path-ext = equivFun (Path.congPathEquiv {A = λ i → ua ρ i} {! !}) {! !}

        to-fin-path : PathP (λ i → ua ρ i ≃ ⟨ Fin (card-path i) ⟩)
          (to-fin (Ps* s f))
          (to-fin (Ps* s f'))
        to-fin-path = equivPathP $ ua→ λ (t , (p , fp≡t) , q) → to-fin-path-ext t p fp≡t q

        goal : Ps* s f ≡ Ps* s f'
        goal = ΣPathP λ where
          .fst → ua ρ
          .snd → ΣPathP λ where
            .fst → card-path
            .snd → to-fin-path

    private
      Ps*-well-defined≈-card : f ≈ f' → card (Ps* s f) ≡ card (Ps* s f')
      Ps*-well-defined≈-card (g , eq) = Fin-inj $ totalSum-permute-snd _ _ (invEquiv (str (P s) .snd) ∙ₑ σ.action g ∙ₑ (str (P s) .snd)) $ funExt
        λ p → cong (card ∘ Q) $
          let α = str (P s) .snd in
          f (invEq α p)
            ≡⟨ eq ≡$ (invEq α p) ⟩
          f' (g σ.▷ (invEq α p))
            ≡[ i ]⟨ f' (retEq α (g σ.▷ invEq α p) (~ i) ) ⟩
          f' (invEq α (equivFun α (g σ.▷ (invEq α p))))
            ∎

    Ps*-well-defined≈ : f ≈ f' → Ps* s f ≡ Ps* s f'
    Ps*-well-defined≈ = FinOrd≡ ∘ Ps*-well-defined≈-card

    Ps*-well-defined' : f ∼ f' → Ps* s f ≡ Ps* s f'
    Ps*-well-defined' = PT.rec (isSetFinOrd _ _) Ps*-well-defined≈

    Ps*-well-defined-β : (g : ⟨ G s ⟩) → (f∼f' : f ≡ f' ∘ (σ s ⁺ g))
      → transport (cong ⟨_⟩ $ Ps*-well-defined' (∃-intro g f∼f')) ≡ invEq (to-fin (Ps* s f')) ∘ subst Fin.Fin (Ps*-well-defined≈-card (g , f∼f')) ∘ equivFun (to-fin (Ps* s f))
    Ps*-well-defined-β g f∼f' = FinOrd≡-β (Ps* s f) (Ps* s f') {p = (Ps*-well-defined≈-card (g , f∼f'))}

  Ps : Sh → FinOrd
  Ps = uncurry λ s → SQ.rec isSetFinOrd (Ps* s) (Ps*-well-defined s)

  module _ s (f f' : ⟨ P s ⟩ → T) (g₀ : ⟨ G s ⟩) (f≡fσg : f ≡ f' ∘ (σ s ⁺ g₀)) where
    private
      f'≡fσg : f' ≡ f ∘ (σ s ⁻ g₀)
      f'≡fσg = σ.precomp-inv g₀ f≡fσg

    restrict-conj : ∀ h → Restrict s f h ≃ Restrict s f' (G.inv g₀ G.· (h G.· g₀))
    restrict-conj h = propBiimpl→Equiv (isPropRestrict _ _ _) (isPropRestrict _ _ _) to from
      where
        to : Restrict s f h → Restrict s f' (G.inv g₀ G.· (h G.· g₀))
        to r t p = compPathlEquiv $
          f' ((G.inv g₀ G.· (h G.· g₀)) σ.▷ p)
            ≡⟨ cong (λ - → f' (- σ.▷ p)) (G.·Assoc _ _ _) ⟩
          f' (((G.inv g₀ G.· h) G.· g₀) σ.▷ p)
            ≡⟨ cong f' (σ.action-comp-ext _ _ _) ⟩
          f' (g₀ σ.▷ ((G.inv g₀ G.· h) σ.▷ p))
            ≡⟨ sym (f≡fσg ≡$ _) ⟩
          f (((G.inv g₀ G.· h) σ.▷ p))
            ≡⟨ cong f (σ.action-comp-ext _ _ _) ⟩
          f (h σ.▷ (G.inv g₀ σ.▷ p))
            ≡⟨ sym (invEq (r _ (G.inv g₀ σ.▷ p)) refl) ⟩
          f (G.inv g₀ σ.▷ p)
            ≡⟨ cong f (σ.action-inv g₀ ≡$ p) ⟩
          f (g₀ σ.▷⁻ p)
            ≡⟨ sym (f'≡fσg ≡$ p) ⟩
          f' p
            ∎

        from : Restrict s f' (G.inv g₀ G.· h G.· g₀) → Restrict s f h
        from r t p = compPathlEquiv $
          f (h σ.▷ p)
            ≡⟨ f≡fσg ≡$ (h σ.▷ p) ⟩
          f' (g₀ σ.▷ (h σ.▷ p))
            ≡⟨ cong f' $ sym $ σ.action-comp-ext _ _ _ ⟩
          f' ((h G.· g₀) σ.▷ p)
            ≡⟨ cong (λ - → f' (- σ.▷ p)) $ sym $ cancel ⟩
          f' ((g₀ G.· (G.inv g₀ G.· (h G.· g₀))) σ.▷ p)
            ≡⟨ cong f' (σ.action-comp-ext _ _ _) ⟩
          f' ((G.inv g₀ G.· (h G.· g₀)) σ.▷ (g₀ σ.▷ p))
            ≡⟨ equivFun (r _ (g₀ σ.▷ p)) refl ⟩
          f' (g₀ σ.▷ p)
            ≡⟨ sym $ f≡fσg ≡$ p ⟩
          f p
            ∎
            where
              cancel : g₀ G.· (G.inv g₀ G.· (h G.· g₀)) ≡ (h G.· g₀)
              cancel = G.·Assoc g₀ (G.inv g₀) _ ∙ cong (G._· (h G.· g₀)) (G.·InvR g₀) ∙ G.·IdL _

    G∣-≃ : GroupEquiv (G∣ s f) (G∣ s f')
    G∣-≃ .fst = Σ-cong-equiv (conjEquiv (G s) g₀) restrict-conj
    G∣-≃ .snd = makeIsGroupHom λ _ _ → Σ≡Prop (isPropRestrict s f') (conjGroupEquiv (G s) g₀ .snd .IsGroupHom.pres· _ _)

    H∣-≃ : GroupEquiv (H∣ s f) (H∣ s f')
    H∣-≃ .fst = equivΠDomain (Σ-cong-equiv-snd λ t → Σ-cong-equiv (invEquiv $ σ.action g₀) λ p → compPathlEquiv $ sym $ f'≡fσg ≡$ p)
    H∣-≃ .snd = makeIsGroupHom λ _ _ → refl

    φ∣-coherence : ∀ h g →
      groupEquivFun H∣-≃ (groupEquivFun (φ∣ s f .fst g) h)
        ≡
      groupEquivFun (φ∣ s f' .fst (groupEquivFun G∣-≃ g)) (groupEquivFun H∣-≃ h)
    φ∣-coherence h (g , r') = funExt λ where
      (t , (p , fp≡t)) → cong h $ ΣPathP λ where
        .fst → refl′ t
        .snd → Σ≡Prop (λ p → is-set-T (f p) t) $
          g σ.▷ (g₀ σ.▷⁻ p)
            ≡⟨ cong (g σ.▷_) $ sym $ σ.action-inv g₀ ≡$ p ⟩
          g σ.▷ (G.inv g₀ σ.▷ p)
            ≡⟨ sym (σ.action-comp-ext _ _ p) ⟩
          (G.inv g₀ G.· g) σ.▷ p
            ≡⟨ sym (retEq (σ.action g₀) _) ⟩
          g₀ σ.▷⁻ (g₀ σ.▷ ((G.inv g₀ G.· g) σ.▷ p))
            ≡⟨ cong (g₀ σ.▷⁻_) $ sym $ σ.action-comp-ext _ _ _ ⟩
          g₀ σ.▷⁻ (((G.inv g₀ G.· g) G.· g₀) σ.▷ p)
            ≡⟨ cong (λ - → g₀ σ.▷⁻ (- σ.▷ p)) $ sym $ G.·Assoc _ _ _ ⟩
          g₀ σ.▷⁻ ((G.inv g₀ G.· (g G.· g₀)) σ.▷ p)
            ∎

    Gr*-≃ : GroupEquiv (Gr* s f) (Gr* s f')
    Gr*-≃ = SemidirectProductEquiv
      {N₀ = H∣ s f} {N₁ = H∣ s f'}
      {H₀ = G∣ s f} {H₁ = G∣ s f'}
      (φ∣ s f) (φ∣ s f')
      H∣-≃ G∣-≃ φ∣-coherence

  GrSub*-well-defined : ∀ s → (f f' : ⟨ P s ⟩ → T)
    → (r : f ≈ f')
    → PathP (λ i → Subgroup (𝔖 (FinOrd→hSet $ Ps (s , SQ.eq/ f f' ∣ r ∣₁ i))) _ / _∼ˢᵘᵇ_) [ GrSub* s f ] [ GrSub* s f' ]
  GrSub*-well-defined s f f' (g₀ , eq) = toPathP $ SQ.eq/ _ _ goal where
      goal' : GroupEquiv (Gr* s f) (Gr* s f')
      goal' = Gr*-≃ s f f' g₀ eq

      goal : GroupEquiv (⟨ Gr* s f ⟩ , transport refl (str (Gr* s f))) (Gr* s f')
      goal = subst (λ - → GroupEquiv (⟨ Gr* s f ⟩ , -) (Gr* s f')) (sym (transportRefl (str (Gr* s f)))) goal'

  GrSub/ : (sh : Sh) → (Subgroup (𝔖 (FinOrd→hSet $ Ps sh)) ℓ-zero) / _∼ˢᵘᵇ_
  GrSub/ = uncurry λ s → SQ.elim (λ f → SQ.squash/) (λ f → [ GrSub* s f ]) λ where
    f f' → PT.elim (λ r → isOfHLevelPathP' 1 SQ.squash/ _ _) (GrSub*-well-defined s f f')

  GrSub : (sh : Sh) → Subgroup (𝔖 (FinOrd→hSet $ Ps sh)) ℓ-zero
  GrSub sh = perm-elim.emb (Ps sh) $ GrSub/ sh

  Gr : Sh → Group ℓ-zero
  Gr = Subgroup.sub ∘ GrSub

  module Gr sh = GroupStr (str (Gr sh))

  ac : (sh : Sh) → Action (Gr sh) (FinOrd→hSet (Ps sh))
  ac sh = GroupHom→Action (inc (GrSub sh))

  -- Computation rules for the subgroup coming from a definable quotient:
  module _ {s} (f : ⟨ P s ⟩ → T) where
    opaque
      GrSub-β : GrSub (s , [ f ]) ≡ GrSub* s f
      GrSub-β = perm-elim.complete (Ps (s , [ f ])) (GrSub* s f)

    Gr-β : Gr (s , [ f ]) ≡ Gr* s f
    Gr-β = cong Subgroup.sub GrSub-β

    Gr-β≃ : ⟨ Gr (s , [ f ]) ⟩ ≃ ⟨ Gr* s f ⟩
    Gr-β≃ = pathToEquiv $ cong ⟨_⟩ $ Gr-β

    Gr-elim : ⟨ Gr (s , [ f ]) ⟩ → ⟨ Gr* s f ⟩
    Gr-elim = equivFun Gr-β≃

    Gr-intro : ⟨ Gr* s f ⟩ → ⟨ Gr (s , [ f ]) ⟩
    Gr-intro = invEq Gr-β≃

    ac-β : (gr : ⟨ Gr (s , [ f ]) ⟩) → ac (s , [ f ]) ⁺ gr ≡ (ac* s f ⁺ Gr-elim gr)
    ac-β gr i = equivFun (inc (GrSub-β i) .fst (transport-filler (cong ⟨_⟩ Gr-β) gr i))
