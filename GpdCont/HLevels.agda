module GpdCont.HLevels where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Data.Empty as Empty using (⊥ ; ⊥*)
open import Cubical.Data.Sigma

private
  variable
    ℓA ℓB : Level
    A : Type ℓA

isProp⊥→ : isProp (⊥ → A)
isProp⊥→ = isContr→isProp Empty.isContr⊥→A

isProp⊥*→ : ∀ {ℓ⊥} → isProp (⊥* {ℓ⊥} → A)
isProp⊥*→ = isContr→isProp Empty.isContrΠ⊥*

ΣOfHLevel : (n : HLevel) (A : TypeOfHLevel ℓA n) (B : ⟨ A ⟩ → TypeOfHLevel ℓB n) → TypeOfHLevel (ℓ-max ℓA ℓB) n
ΣOfHLevel n A B .fst = Σ ⟨ A ⟩ (⟨_⟩ ∘ B)
ΣOfHLevel n A B .snd = isOfHLevelΣ n (str A) (str ∘ B)

syntax ΣOfHLevel n A (λ a → B) = Σʰ[ n ∣ a ∈ A ] B

ΠOfHLevel : (n : HLevel) (A : Type ℓA) (B : A → TypeOfHLevel ℓB n) → TypeOfHLevel (ℓ-max ℓA ℓB) n
ΠOfHLevel n A B .fst = ∀ a → ⟨ B a ⟩
ΠOfHLevel n A B .snd = isOfHLevelΠ n (str ∘ B)

syntax ΠOfHLevel n A (λ a → B) = Πʰ[ n ∣ a ∈ A ] B

→OfHLevel : (n : HLevel) (A : Type ℓA) (B : TypeOfHLevel ℓB n) → TypeOfHLevel (ℓ-max ℓA ℓB) n
→OfHLevel n A B .fst = A → ⟨ B ⟩
→OfHLevel n A B .snd = isOfHLevelΠ n (λ _ → str B)

syntax →OfHLevel n A B = A →[ n ] B

_→₃_ : (A : Type ℓA) → (B : hGroupoid ℓB) → hGroupoid (ℓ-max ℓA ℓB)
_→₃_ = →OfHLevel 3
