module GpdCont.QuotientContainer.Premorphism where

open import GpdCont.Prelude
open import GpdCont.QuotientContainer.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (isEquivInvEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (Jequiv)
open import Cubical.Functions.Image
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom ; GroupHom≡)
import Cubical.HITs.PropositionalTruncation as PT

module _ {ℓ} (Q R : QCont ℓ) (shape-mor : Q .QCont.Shape → R .QCont.Shape) where
  private
    module Q = QCont Q
    module R = QCont R

  isNaturalFiller : (f : ∀ s → R.Pos (shape-mor s) → Q.Pos s)
    → ∀ {s} (g : Q.Symm s) (h : R.Symm (shape-mor s))
    → Type _
  isNaturalFiller f {s} g h = (f s Q.▷ g) ≡ (h R.◁ f s)

  record Premorphism : Type ℓ where
    no-eta-equality

    field
      pos-mor : ∀ (s : Q.Shape) → R.Pos (shape-mor s) → Q.Pos s

    field
      symm-pres : ∀ (s : Q.Shape) (g : Q.Symm s) → ∃[ h ∈ (R.Symm (shape-mor s)) ] isNaturalFiller pos-mor g h
      -- symm-pres : ∀ (s : Q.Shape) → Q.Symm s → R.Symm (shape-mor s)
      -- symm-pres-natural : ∀ (s : Q.Shape) (σ : Q.Symm s)
      --   → pos-mor s Q.▷ σ ≡ (symm-pres s σ) R.◁ (pos-mor s)

      -- The morphism of shapes preserves the subgroup of symmetries, naturally:
      --
      --                           pos-mor s
      --      R.Pos (shape-mor s) ------------> Q.Pos s
      --               |                           |
      --               |                           |
      -- symm-pres s σ |                           | σ
      --               |                           |
      --               v                           v
      --      R.Pos (shape-mor s) ------------> Q.Pos s
      --                           pos-mor s

    -- private opaque
    --   symm-pres-is-group-hom : ∀ s → IsGroupHom (Q.SymmGroupStr s) (symm-pres s) (R.SymmGroupStr (shape-mor s))
    --   symm-pres-is-group-hom s = makeIsGroupHom pres· where
    --     pres· : ∀ σ τ → symm-pres s (σ Q.· τ) ≡ (symm-pres s σ) R.· (symm-pres s τ)
    --     pres· σ τ = {! !}

    -- private opaque
    --   isInjectivePosMor→isGroupHomSymPres : ∀ s
    --     → (∀ {x y} → pos-mor s x ≡ pos-mor s y → x ≡ y)
    --     → IsGroupHom (Q.SymmGroupStr s) (symm-pres s) (R.SymmGroupStr (shape-mor s))
    --   isInjectivePosMor→isGroupHomSymPres s inj-pos-mor = makeIsGroupHom pres· where
    --     cancel : ∀ {X : Type ℓ} (f f′ : X → R.Pos (shape-mor s)) → pos-mor s ∘ f ≡ pos-mor s ∘ f′ → f ≡ f′
    --     cancel f f′ p = funExt λ x → inj-pos-mor (funExt⁻ p x)

    --     pres·-comp-pos-mor : ∀ σ τ →
    --       symm-pres s (σ Q.· τ) R.◁ pos-mor s ≡ ((symm-pres s σ) R.· (symm-pres s τ)) R.◁ pos-mor s
    --     pres·-comp-pos-mor σ τ =
    --       let Φ = symm-pres s
    --           f = pos-mor s
    --           Φ-nat = symm-pres-natural s
    --       in
    --       Φ (σ Q.· τ) R.◁ f     ≡⟨ sym (Φ-nat (σ Q.· τ)) ⟩
    --       f Q.▷ (σ Q.· τ)       ≡⟨⟩
    --       (f Q.▷ σ) Q.▷ τ       ≡⟨ cong (λ - → - Q.▷ τ) (Φ-nat σ) ⟩
    --       (Φ σ R.◁ f) Q.▷ τ     ≡⟨⟩
    --       τ Q.⁺ ∘ (f ∘ Φ σ R.⁺) ≡⟨⟩
    --       Φ σ R.◁ (f Q.▷ τ)     ≡⟨ cong (λ - → Φ σ R.◁ -) (Φ-nat τ) ⟩
    --       Φ σ R.◁ (Φ τ R.◁ f)   ≡⟨⟩
    --       (Φ σ R.· Φ τ) R.◁ f ∎

    --     pres· : ∀ σ τ → symm-pres s (σ Q.· τ) ≡ (symm-pres s σ) R.· (symm-pres s τ)
    --     pres· σ τ = R.Eq⁺ $
    --       cancel
    --         (symm-pres s (σ Q.· τ) R.⁺)
    --         ((symm-pres s σ R.· symm-pres s τ) R.⁺)
    --         (pres·-comp-pos-mor σ τ)

    -- symmHom : ∀ (s : Q.Shape) → GroupHom (Q.SymmGroup s) (R.SymmGroup (shape-mor s))
    -- symmHom s .fst = symm-pres s
    -- symmHom s .snd = symm-pres-is-group-hom s

unquoteDecl PremorphismIsoΣ = declareRecordIsoΣ PremorphismIsoΣ (quote Premorphism)

instance
  PremorphismToΣ : ∀ {ℓ} {Q R : QCont ℓ} {shape-mor : Q .QCont.Shape → R .QCont.Shape} → RecordToΣ (Premorphism Q R shape-mor)
  PremorphismToΣ {Q} {R} = toΣ PremorphismIsoΣ

module _ {ℓ} {Q R : QCont ℓ}  {shape-mor : Q .QCont.Shape → R .QCont.Shape} (f g : Premorphism Q R shape-mor) where
  private
    module Q = QCont Q
    module R = QCont R
    open Premorphism

  record PremorphismEquiv∞ : Type ℓ where
    --                          η(s)
    --  R.Pos (shape-mor s) -----------> R.Pos (shape-mor s)
    --          |                                |
    --     f(s) |                                | g(s)
    --          '-----------> Q.Pos s <----------'
    field
      η : (s : Q.Shape) → R.Symm (shape-mor s)
      η-comm : ∀ s → f .pos-mor s ≡ (η s R.◁ g .pos-mor s)
  
  PremorphismEquiv : Type ℓ
  PremorphismEquiv = ∀ (s : Q.Shape) → ∃[ ρ ∈ R.Symm (shape-mor s) ] f .pos-mor s ≡ ρ R.◁ g .pos-mor s

private
  variable
    ℓ : Level
    Q R S T : QCont ℓ

open QCont

open Premorphism

module _ {ℓ} {Q R : QCont ℓ} where
  private
    module R = QCont R
  PremorphismEquiv' : {u u′ : Q .Shape → R .Shape} → (f : Premorphism Q R u) → (f′ : Premorphism Q R u′) → Type _
  PremorphismEquiv' {u} {u′} f f′ =
    Σ[ p ∈ u ≡ u′ ]
      ∀ s → ∃[ ρ ∈ R.Symm (u s) ] (f .pos-mor s ≡ (ρ R.⁺) ⋆ r p ⋆ f′ .pos-mor s)
    where
      r : (p : u ≡ u′) → ∀ {s} → R .Pos (u s) → R .Pos (u′ s)
      r p = subst (R .Pos) (funExt⁻ p _)

  -- foo : (u : Q .Shape → R .Shape) → {! !}
  -- foo u =
  --   (∀ u′ → ∀ f f′ → PremorphismEquiv' {u} {u′} f f′) ≃⟨⟩
  --   (∀ u′ → ∀ f f′ → Σ[ p ∈ u ≡ u′ ] ∀ s → ∃[ ρ ∈ R.Symm (u s) ] (f .pos-mor s ≡ (ρ R.⁺) ⋆ subst (R .Pos) (funExt⁻ p s) ⋆ f′ .pos-mor s)) ≃⟨ {! !} ⟩
  --   (∀ f f′ → PremorphismEquiv {Q = Q} {R = R} {shape-mor = u} f f′) ≃∎

opaque
  private
    isPropSymmPres : {shape-mor : Q .Shape → R .Shape} (pos-mor : ∀ s → R .Pos (shape-mor s) → Q .Pos s) → isProp (∀ (s : Q .Shape) → (g : Symm Q s) → ∃[ h ∈ (Symm R (shape-mor s)) ] isNaturalFiller Q R _ pos-mor g h)
    isPropSymmPres pos-mor = isPropΠ2 λ s g → isProp∃ _ _

  isSetPremorphism : {shape-mor : Q .Shape → R .Shape} → isSet (Premorphism Q R shape-mor)
  isSetPremorphism {Q} {R} {shape-mor} = recordIsOfHLevel 2 $
    isSetΣSndProp (isSetΠ2 (λ _ _ → Q .is-set-pos _)) $
    isPropSymmPres {Q = Q} {R = R}
  -- isSetΣ (isSetΠ2 (λ _ _ → Q .is-set-pos _))
  -- λ pos-mor → isSetΣSndProp (isSetΠ2 λ _ _ → isSetSymm R)
  -- λ symm-pres → isPropΠ2 λ _ _ → isOfHLevelPath' 1 (isSetΠ λ _ → Q .is-set-pos _) _ _

module _ (Q : QCont ℓ) where
  private
    module Q = QCont Q

  idPremorphism : Premorphism Q Q (id _)
  idPremorphism .pos-mor = id ∘ Q.Pos
  idPremorphism .symm-pres s g = ∃-intro g refl -- id ∘ Q.Symm

isReflPremorphismEquiv : ∀ {shape-mor : Q .Shape → R .Shape} → (f : Premorphism Q R shape-mor) → PremorphismEquiv f f
isReflPremorphismEquiv {Q} {R} {shape-mor} f = λ s → ∃-intro (ρ s) refl where
  module Q = QCont Q
  module R = QCont R
  ρ : (s : Q.Shape) → R.Symm (shape-mor s)
  ρ = R.SymmGroup.1g ∘ shape-mor


PremorphismPath : ∀ {shape-mor : Q .QCont.Shape → R .QCont.Shape} {f g : Premorphism Q R shape-mor}
  → (f .pos-mor ≡ g .pos-mor)
  → f ≡ g
PremorphismPath {Q} {R} {shape-mor} {f} {g} pos-mor-path = λ
  { i .pos-mor → pos-mor-path i
  ; i .symm-pres → isProp→PathP (λ i → isPropSymmPres {Q = Q} {R = R} (pos-mor-path i)) (f .symm-pres) (g .symm-pres) i
  -- ; i .symm-pres-natural s σ → isProp→PathP
  --   {B = λ i → pos-mor-path i s Q.▷ σ ≡ (symm-pres-path i s σ) R.◁ (pos-mor-path i s)}
  --   (λ i → isOfHLevelPath' 1 (isSet→ (Q.is-set-pos s)) _ _) (f .symm-pres-natural s σ) (g .symm-pres-natural s σ) i
  }
  where private
    module Q = QCont Q
    module R = QCont R

module Composite
  {u : Q .Shape → R .Shape} {v : R .Shape → S .Shape}
  (f : Premorphism Q R u) (g : Premorphism R S v)
  where
  private
    module Q = QCont Q
    module R = QCont R
    module S = QCont S
  
  comp-pos-mor : ∀ s → S.Pos (u ⋆ v $ s) → Q.Pos s
  comp-pos-mor s = g .pos-mor (u s) ⋆ f .pos-mor s

  -- comp-pos-symm-pres : ∀ s (σ : Q.Symm s) → S.Symm (u ⋆ v $ s)
  -- comp-pos-symm-pres s σ = g .symm-pres (u s) $ (f .symm-pres s σ)

  -- opaque
  --   compPremorphism-symm-pres-natural : ∀ s (σ : Q.Symm s) → (comp-pos-mor s) Q.▷ σ ≡ (comp-pos-symm-pres s σ) S.◁ (comp-pos-mor s)
  --   compPremorphism-symm-pres-natural s σ =
  --     g .pos-mor (u s) ⋆ f .pos-mor s ⋆ σ Q.⁺ ≡⟨ cong (g .pos-mor _ ⋆_) (f .symm-pres-natural s σ) ⟩
  --     g .pos-mor (u s) ⋆ f .symm-pres s σ R.⁺ ⋆ f .pos-mor s ≡⟨ cong (_⋆ f .pos-mor s) (g .symm-pres-natural (u s) (f .symm-pres s σ)) ⟩
  --     (g .symm-pres (u s) (f .symm-pres s σ)) S.⁺ ⋆ (g .pos-mor (u s) ⋆ f .pos-mor s) ∎

  compPremorphism : Premorphism Q S (u ⋆ v)
  compPremorphism .pos-mor = comp-pos-mor
  compPremorphism .symm-pres s ψ = goal where
    open import Cubical.HITs.PropositionalTruncation.Monad using (_>>=_ ; return)

    opaque
      lem : (ρ : R.Symm _) → isNaturalFiller Q R u (f .pos-mor) ψ ρ
        → (σ : S.Symm _) → isNaturalFiller R S v (g .pos-mor) ρ σ
        → isNaturalFiller Q S (u ⋆ v) comp-pos-mor ψ σ
      lem ρ ρ-nat σ σ-nat =
        g .pos-mor _ ⋆ f .pos-mor _ ⋆ (ψ Q.⁺) ≡⟨ cong (g .pos-mor _ ⋆_) ρ-nat ⟩
        g .pos-mor _ ⋆ (ρ R.⁺) ⋆ f .pos-mor _ ≡⟨ cong (_⋆ f .pos-mor _) σ-nat ⟩
        (σ S.⁺) ⋆ g .pos-mor _ ⋆ f .pos-mor _ ∎

      goal : ∃[ τ ∈ S.Symm _ ] isNaturalFiller Q S (u ⋆ v) comp-pos-mor ψ τ
      goal = do
        (ρ , ρ-nat) ← (f .symm-pres s ψ)
        (σ , σ-nat) ← (g .symm-pres (u s) ρ)
        return $ σ , lem ρ ρ-nat σ σ-nat

open Composite using () renaming (compPremorphism to _⋆-pre_)

opaque
  ⋆IdL : (u : Q .Shape → R .Shape) (f : Premorphism Q R u) → (idPremorphism Q) ⋆-pre f ≡ f
  ⋆IdL u f = PremorphismPath refl

  ⋆IdR : (u : Q .Shape → R .Shape) (f : Premorphism Q R u) → f ⋆-pre (idPremorphism R) ≡ f
  ⋆IdR u f = PremorphismPath refl

  ⋆Assoc : (u : Q .Shape → R .Shape) (v : R .Shape → S .Shape) (w : S .Shape → T .Shape)
    → (f : Premorphism Q R u)
    → (g : Premorphism R S v)
    → (h : Premorphism S T w)
    → (f ⋆-pre g) ⋆-pre h ≡ f ⋆-pre (g ⋆-pre h)
  ⋆Assoc u v w f g h = PremorphismPath refl

-- opaque
--   isWellDefinedSymmHom : ∀ {s} {u : Q .Shape → R .Shape} (f f′ : Premorphism Q R u) → PremorphismEquiv f f′ → symmHom f s ≡ symmHom f′ s
--   isWellDefinedSymmHom {Q} {s} f f′ r = GroupHom≡ $ funExt goal where
--     open PremorphismEquiv r using (η ; η-comm)
--     open Premorphism f using () renaming (symm-pres to φ)
--     open Premorphism f′ using () renaming (symm-pres to φ′)

--     goal : (σ : Symm Q s) →  φ s σ ≡ φ′ s σ
--     goal σ = {! φ s !}

record NormalMorphism {ℓ} (Q R : QCont ℓ) (shape-mor : Q .QCont.Shape → R .QCont.Shape) : Type ℓ where
  no-eta-equality
  private
    module Q = QCont Q
    module R = QCont R

  field
    pos-mor-n : ∀ (s : Q.Shape) → R.Pos (shape-mor s) → Q.Pos s

  field
    symm-pres-n : ∀ (s : Q.Shape) → Q.Symm s → R.Symm (shape-mor s)
    symm-pres-is-hom : ∀ {s} → IsGroupHom (Q.SymmGroupStr s) (symm-pres-n s) (R.SymmGroupStr (shape-mor s))
    symm-pres-natural-n : ∀ (s : Q.Shape) (σ : Q.Symm s)
      → pos-mor-n s Q.▷ σ ≡ (symm-pres-n s σ) R.◁ (pos-mor-n s)

pre→normal : ∀ {Q R : QCont ℓ} (u : Q .QCont.Shape → R .QCont.Shape) → Premorphism Q R u → NormalMorphism Q R u
pre→normal {Q} {R} u f = goal where
  goal : NormalMorphism Q R u
  goal .NormalMorphism.pos-mor-n = f .pos-mor
  goal .NormalMorphism.symm-pres-n = {! !}
  goal .NormalMorphism.symm-pres-is-hom = {! !}
  goal .NormalMorphism.symm-pres-natural-n = {! !}
  {-# INLINE goal #-}
