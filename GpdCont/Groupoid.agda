module GpdCont.Groupoid where

open import GpdCont.Prelude
open import GpdCont.RecordEquiv

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

record GroupStr {ℓ} (G : Type ℓ) : Type ℓ where
  field
    is-connected : isContr ∥ G ∥₂
    is-groupoid : isGroupoid G
    pt : G

Group : (ℓ : Level) → Type _
Group ℓ = TypeWithStr ℓ GroupStr

unquoteDecl GroupStrIsoΣ = declareRecordIsoΣ GroupStrIsoΣ (quote GroupStr)

private
  variable
    ℓ : Level
    G : Type ℓ

instance
  GroupStrToΣ : RecordToΣ (GroupStr G)
  GroupStrToΣ = toΣ GroupStrIsoΣ

open GroupStr

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
