module GpdCont.HomotopySet where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels using (hSet) public
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma as Sigma using (_×_)
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Empty as Empty using (⊥*)
open import Cubical.Data.Unit as Unit using (Unit*)

private
  variable
    ℓ ℓ' : Level
    X Y : hSet ℓ

hSet≡ : ⟨ X ⟩ ≡ ⟨ Y ⟩ → X ≡ Y
hSet≡ = TypeOfHLevel≡ 2

hSet≡Equiv⁻ : (X ≡ Y) ≃ (⟨ X ⟩ ≡ ⟨ Y ⟩)
hSet≡Equiv⁻ .fst = cong ⟨_⟩
hSet≡Equiv⁻ .snd = Sigma.isEmbeddingFstΣProp λ _ → isPropIsSet

hSet≡Equiv : (⟨ X ⟩ ≡ ⟨ Y ⟩) ≃ (X ≡ Y)
hSet≡Equiv = Sigma.Σ≡PropEquiv λ _ → isPropIsSet

hSet≡-section : ∀ {X Y : hSet ℓ} → section (hSet≡ {X = X} {Y = Y}) (cong ⟨_⟩)
hSet≡-section = retEq hSet≡Equiv⁻

_→Set_ : (X : hSet ℓ) (Y : hSet ℓ') → hSet _
_→Set_ X Y .fst = ⟨ X ⟩ → ⟨ Y ⟩
_→Set_ X Y .snd = isSet→ $ str Y

ΠSet : {S : Type ℓ} (X : S → hSet ℓ') → hSet _
ΠSet X .fst = ∀ s → ⟨ X s ⟩
ΠSet X .snd = isSetΠ $ str ∘ X

ΠSet' : {S : Type ℓ} (X : S → Type ℓ') → (∀ s → isSet (X s)) → hSet _
ΠSet' X is-set-X = ΠSet λ s → X s , is-set-X s

_×Set_ : (X : hSet ℓ) (Y : hSet ℓ') → hSet _
(X ×Set Y) .fst = ⟨ X ⟩ × ⟨ Y ⟩
(X ×Set Y) .snd = isSet× (str X) (str Y)

_⊎Set_ : (X : hSet ℓ) (Y : hSet ℓ') → hSet _
(X ⊎Set Y) .fst = ⟨ X ⟩ ⊎ ⟨ Y ⟩
(X ⊎Set Y) .snd = Sum.isSet⊎ (str X) (str Y)

ΣSet : (X : hSet ℓ) (Y : ⟨ X ⟩ → hSet ℓ') → hSet _
ΣSet X Y .fst = Σ ⟨ X ⟩ $ ⟨_⟩ ∘ Y
ΣSet X Y .snd = isSetΣ (str X) (str ∘ Y)

EmptySet : (ℓ : Level) → hSet ℓ
EmptySet ℓ .fst = ⊥*
EmptySet ℓ .snd = isProp→isSet Empty.isProp⊥*

UnitSet : (ℓ : Level) → hSet ℓ
UnitSet ℓ .fst = Unit*
UnitSet ℓ .snd = Unit.isSetUnit*
