module GpdCont.Analytic.Synthetic where

open import GpdCont.Prelude
open import GpdCont.HomotopySet

open import GpdCont.StrictGroupoid.Base
open import GpdCont.StrictGroupoid.Properties
open import GpdCont.StrictGroupoid.HomotopyGroup
open import GpdCont.StrictGroupoid.Discrete

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet as FinSet using (isFinSet)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)


module _ {ℓ}
  (S T : Type ℓ)
  (P : S → Type ℓ)
  (Q : T → Type ℓ)
  (is-fin-P : ∀ s → isFinSet (P s))
  (is-fin-Q : ∀ t → isFinSet (Q t))
  (strict-S : StrictGroupoidStr S)
  (strict-T : StrictGroupoidStr T)
  where

  private
    module S = StrictGroupoidStr strict-S
    module T = StrictGroupoidStr strict-T

    is-set-P : ∀ s → isSet (P s)
    is-set-P s = FinSet.isFinSet→isSet (is-fin-P s)
    
    G : StrictGroupoid ℓ
    G .fst = S
    G .snd = strict-S

    X : S → hSet ℓ
    X s .fst = P s
    X s .snd = is-set-P s
    -- X s .fst = P s × (Σ[ x ∈ ∥ S ∥₂ ] ∣ s ∣₂ ≡ x)
    -- X s .snd = isSet× (is-set-P s) $ isSetΣSndProp ST.isSetSetTrunc λ x → ST.isSetSetTrunc _ _

    H : (s : S) → P s → hGroup ℓ
    H _ _ = ΠGroup T (Aut (_ , T.is-groupoid))

    -- H' : (s : S) → P s → hGroup ℓ
    -- H' _ _ = ⨁Group T (Aut (_ , T.is-groupoid))

    G' : StrictGroupoid ℓ
    G' = G ×ˢ discrete (∥ T ∥₂ , ST.isSetSetTrunc)

    X' : ⟨ G' ⟩ → hSet ℓ
    X' (s , y) = X s

    -- H' : ⟨ G' ⟩ → hGroup ℓ
    -- H' (g , y) = Aut (_ , T.is-groupoid) (T.pt y)
    H' : ∀ g' → (⟨ X' g' ⟩) → hGroup ℓ
    H' (s , y) _ = Aut (_ , T.is-groupoid) (T.pt y)

  U : StrictGroupoid _
  U = Wrˢ G X H

  Uᵝ : ⟨ U ⟩ ≡ (Σ[ s ∈ S ] (Σ[ f ∈ (P s → Σ[ t* ∈ ((t : T) → fiber ∣_∣₂ ∣ t ∣₂) ] _) ] _))
  Uᵝ = refl

  U' : StrictGroupoid _
  U' = Wrˢ G' X' H'

  U'ᵝ : ⟨ U' ⟩ ≡ (Σ[ (s , y) ∈ (S × ∥ T ∥₂) ] Σ[ f ∈ (P s → Σ[ t ∈ T ] ∣ t ∣₂ ≡ ∣ T.pt y ∣₂) ] (∣ f ∣₂ ≡ ∣ const (T.pt y , refl) ∣₂))
  U'ᵝ = refl

  U'ᵝ≃ : ⟨ U' ⟩ ≃ (Σ[ s ∈ S ] (P s → T))
  U'ᵝ≃ =
    ⟨ U' ⟩ ≃⟨ {! !} {- finiteness of P s -} ⟩
    (Σ[ (s , y) ∈ (S × ∥ T ∥₂) ] (P s → Σ[ t ∈ T ] ∣ t ∣₂ ≡ ∣ T.pt y ∣₂)) ≃⟨ {! !} ⟩
    (Σ[ (s , y) ∈ (S × ∥ T ∥₂) ] (P s → Σ[ t ∈ T ] ∣ t ∣₂ ≡ y)) ≃⟨ {! !} ⟩
    (Σ[ (s , y) ∈ (S × ∥ T ∥₂) ] Σ[ f ∈ (P s → T) ] ∀ p → ∣ f p ∣₂ ≡ y) ≃⟨ {! !} ⟩
    (Σ[ s ∈ S ] Σ[ f ∈ (P s → T) ] Σ[ y ∈ ∥ T ∥₂ ] ((p : P s) → ∣ f p ∣₂ ≡ y)) ≃⟨ {! !} ⟩
    (Σ[ s ∈ S ] Σ[ f ∈ (P s → T) ] Σ[ y ∈ ∥ T ∥₂ ] (∣_∣₂ ∘ f ≡ const y)) ≃⟨ {! !} ⟩
    (Σ[ s ∈ S ] (P s → T)) ≃∎ where

    lemma : (s : S) (f : P s → T) → isProp (Σ[ y ∈ ∥ T ∥₂ ] (∣_∣₂ ∘ f ≡ const y))
    lemma s f (y , p) (y' , p') = Σ≡Prop (λ _ → ?) y≡y' where
      y≡y' : y ≡ y'
      y≡y' = {!sym p ∙ p'  !}


  -- U'ᵝ≃ : ⟨ U' ⟩ ≃ (Σ[ s ∈ S ] (P s → T))
  -- U'ᵝ≃ =
  --   ⟨ U' ⟩ ≃⟨ {! !} {- finiteness of P s -} ⟩
  --   (Σ[ (s , y) ∈ (S × ∥ T ∥₂) ] (P s → Σ[ t ∈ T ] ∣ t ∣₂ ≡ ∣ T.pt y ∣₂)) ≃⟨ {! !} ⟩
  --   (Σ[ (s , y) ∈ (S × ∥ T ∥₂) ] (P s → Σ[ t ∈ T ] ∣ t ∣₂ ≡ y)) ≃⟨ {! !} ⟩
  --   (Σ[ (s , y) ∈ (S × ∥ T ∥₂) ] Σ[ f ∈ (P s → T) ] ∀ p → ∣ f p ∣₂ ≡ y) ≃⟨ {! !} ⟩
  --   (Σ[ s ∈ S ] Σ[ f ∈ (P s → T) ] Σ[ y ∈ ∥ T ∥₂ ] ((p : P s) → ∣ f p ∣₂ ≡ y)) ≃⟨ {! !} ⟩
  --   (Σ[ s ∈ S ] Σ[ f ∈ (P s → T) ] Σ[ y ∈ ∥ T ∥₂ ] (∣_∣₂ ∘ f ≡ const y)) ≃⟨ {! !} ⟩
  --   (Σ[ s ∈ S ] (P s → T)) ≃∎
