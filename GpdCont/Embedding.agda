module GpdCont.Embedding where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv-snd)
open import Cubical.Reflection.StrictEquiv
open import Cubical.Functions.Embedding public

private
  variable
    ℓ : Level
    A B : Type ℓ
    f : A → B

private
  symEquiv : ∀ {a b : A} → (a ≡ b) ≃ (b ≡ a)
  symEquiv = strictEquiv sym sym

hasContrFiberOfImage→isEmbedding : ((x : A) → isContr (fiber f (f x))) → isEmbedding f
hasContrFiberOfImage→isEmbedding contr-fib-of-im = hasPropFibersOfImage→isEmbedding (isContr→isProp ∘ contr-fib-of-im)

isCancellable→isEmbedding : ((x y : A) → (x ≡ y) ≃ (f x ≡ f y)) → isEmbedding f
isCancellable→isEmbedding {f} cancel-equiv = hasContrFiberOfImage→isEmbedding contr-fib-of-im where
  singl-fiber-equiv : ∀ x → singl x ≃ fiber f (f x)
  singl-fiber-equiv x = Σ-cong-equiv-snd λ y → cancel-equiv x y ∙ₑ symEquiv

  contr-fib-of-im : ∀ x → isContr (fiber f (f x))
  contr-fib-of-im x = isOfHLevelRespectEquiv 0 (singl-fiber-equiv x) (isContrSingl x)
  
