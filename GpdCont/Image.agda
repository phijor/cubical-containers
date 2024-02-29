open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Displayed.Base using (UARel)
open import Cubical.Functions.Embedding
open import Cubical.HITs.Replacement as Replacement using (Replacement)

module GpdCont.Image {ℓA ℓB ℓ≡} {A : Type ℓA} {B : Type ℓB}
  (locally-small : UARel B ℓ≡)
  (f : A → B)
  where

private
  open module ≡B = UARel locally-small using () renaming (_≅_ to _≡B_ ; ua to uaB)

Image : Type (ℓ-max ℓA ℓ≡)
Image = Replacement locally-small f

imageInclusion : Image → B
imageInclusion = Replacement.unrep locally-small f

imageRestriction : A → Image
imageRestriction = Replacement.rep

elimProp : {ℓ : Level} {P : Image → Type ℓ}
  → (∀ x → isProp (P x))
  → ((x : A) → P (imageRestriction x))
  → ∀ x → P x
elimProp = Replacement.elimProp locally-small f

recProp : {ℓ : Level} {P : Type ℓ} → isProp P → (A → P) → (Image → P)
recProp is-prop-P = elimProp (const is-prop-P)

opaque
  -- TODO: Prove hasPropFibers separately in cubical library.
  isEmbeddingImageInclusion : isEmbedding imageInclusion
  isEmbeddingImageInclusion = Replacement.isEmbeddingUnrep _ _

  hasPropFibersImageInclusion : hasPropFibers imageInclusion
  hasPropFibersImageInclusion = isEmbedding→hasPropFibers isEmbeddingImageInclusion

isInImage : (b : B) → Type (ℓ-max ℓA ℓ≡)
isInImage b = Σ[ b′ ∈ Image ] (imageInclusion b′ ≡B b)

isInImage≃fiberImageInclusion : ∀ b → fiber imageInclusion b ≃ isInImage b
isInImage≃fiberImageInclusion b = Σ-cong-equiv-snd  λ b′ → invEquiv (uaB (imageInclusion b′) b)

opaque
  isPropIsInImage : ∀ b → isProp (isInImage b)
  isPropIsInImage b = isOfHLevelRespectEquiv 1
    (isInImage≃fiberImageInclusion b)
    (hasPropFibersImageInclusion b)

map′ : (g : A → A) → Image → Image
map′ g (Replacement.rep a) = Replacement.rep (g a)
map′ g (Replacement.quo r r' r≅r' i) = Replacement.quo (map′ g r) (map′ g r') p i where
  p : imageInclusion (map′ g r) ≡B imageInclusion (map′ g r')
  -- p = ≡B.≡→≅ (cong {x = r} {y = r'} (imageInclusion ∘ map′ g) {!≅→≡ r≅r' !})
  p = ≡B.≡→≅ {!cong {x = r} {y = r'} (map′ g) !}

map : (g : A → A) → Image → Image
map g r = fst (elimProp {P = Motive} isPropMotive g′ r) where
  Motive : Image → Type _
  Motive r = fiber imageInclusion (imageInclusion r)

  isPropMotive : ∀ r → isProp (Motive r)
  isPropMotive r = hasPropFibersImageInclusion (imageInclusion r)

  g′ : (a : A) → Motive (imageRestriction a)
  g′ a .fst = imageRestriction (g a)
  g′ a .snd = {!Replacement.quo !}
