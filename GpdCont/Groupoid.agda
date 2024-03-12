-- TODO:
-- 1. Rename this to GpdCont.Skeleton
-- 2. Define `Skeleton` as the data for a skeleton
-- 3. Re-define `isSkeletal` to `hasSkeleton` / `isSkeletal` via (mere) path to some `Skeleton`
module GpdCont.Groupoid where

open import GpdCont.Prelude
open import GpdCont.RecordEquiv
open import GpdCont.Groups.Base using (GroupStr ; Group)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  variable
    ℓ : Level
    G : Type ℓ

open GroupStr

record Skeleton (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Index : Type ℓ
    Component : Index → Type ℓ

  Total : Type ℓ
  Total = Σ Index Component

  field
    is-set-index : isSet Index
    group-str-component : ∀ (k : Index) → GroupStr (Component k)

  ComponentGroup : Index → Group ℓ
  ComponentGroup k .fst = Component k
  ComponentGroup k .snd = group-str-component k

  open module ComponentGroupStr k = GroupStr (group-str-component k)
    public
    using ()
    renaming (pt to component)

record isSkeletal (G : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    Component : ∥ G ∥₂ → Type ℓ

  field
    group-str-component : ∀ x → GroupStr (Component x)

  Total : Type ℓ
  Total = Σ ∥ G ∥₂ Component

  field
    total-path : G ≡ Total

  component-pt : ∀ x → Component x
  component-pt x = group-str-component x .pt

  isGroupoidTotal : isGroupoid Total
  isGroupoidTotal = isGroupoidΣ (isSet→isGroupoid ST.isSetSetTrunc) (is-groupoid ∘ group-str-component)

  isGroupoid⟨-⟩ : isGroupoid G
  isGroupoid⟨-⟩ = subst isGroupoid (sym total-path) isGroupoidTotal

Skeletal : (ℓ : Level) → Type (ℓ-suc ℓ)
Skeletal ℓ = TypeWithStr ℓ isSkeletal

isPropIsSkeletal : (G : Type ℓ) → isProp (isSkeletal G)
isPropIsSkeletal G s₀ s₁ = {! !} where
  module s₀ = isSkeletal s₀
  module s₁ = isSkeletal s₁

  singleton-coherence : Path (singl G) (s₀.Total , s₀.total-path) (s₁.Total , s₁.total-path)
  singleton-coherence = isPropSingl {a = G} (s₀.Total , s₀.total-path) (s₁.Total , s₁.total-path)

  Component-path : s₀.Component ≡ s₁.Component
  Component-path = funExt (ST.elim (λ x → {! !}) λ g → {!cong snd singleton-coherence !})

isSkeletal′ : (G : Type ℓ) → Type _
isSkeletal′ {ℓ} G = ∀ (g h : G) → isEquiv (λ (p : g ≡ h) → PT.∣ p ∣₁)

isSkeletal′→isSkeletal : isSkeletal′ G → isSkeletal G
isSkeletal′→isSkeletal {G} skel′ = go where
  go : isSkeletal _
  go .isSkeletal.Component = {! !}
  go .isSkeletal.group-str-component = {! !}
  go .isSkeletal.total-path = {! !}

isSkeletal→isSkeletal′ : isSkeletal G → isSkeletal′ G
isSkeletal→isSkeletal′ skel g h .equiv-proof = goal where
  foo : ∀ p → isContr (fiber _ PT.∣ p ∣₁)
  foo p .fst .fst = p
  foo p .fst .snd = refl
  foo p .snd (q , ∣q∣≡∣p∣) = ΣPathP ({!skel  !} , {! !})

  goal : ∀ x → isContr (fiber _ x)
  goal = PT.elim (λ _ → isPropIsContr) foo
