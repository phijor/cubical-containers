module GpdCont.Image.Large where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma.Properties using (map-snd)
open import Cubical.Functions.Image
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

private
  variable
    ℓ : Level
    A B C : Type ℓ
    f : A → B

imageSurjection : (f : A → B) → A ↠ Image f
imageSurjection f .fst = restrictToImage f
imageSurjection f .snd = isSurjectionImageRestriction f

postCompEmbedding→imagesEquiv : {f : A → B} (e : B ↪ C) → Image (e .fst ∘ f) ≃ Image f
postCompEmbedding→imagesEquiv {A} {B} {C} {f} e = imagesEquiv
  (imageSurjection (e⁺ ∘ f)) (imageInclusion (e⁺ ∘ f))
  (imageSurjection f) emb-e∘Im-f
  refl where
  e⁺ : B → C
  e⁺ = e .fst

  emb-e∘Im-f : Image f ↪ C
  emb-e∘Im-f = compEmbedding e (imageInclusion f)

postCompEquiv→imagesEquiv : {f : A → B} (e : B ≃ C) → Image (equivFun e ∘ f) ≃ Image f
postCompEquiv→imagesEquiv e = postCompEmbedding→imagesEquiv (Equiv→Embedding e)

preCompSurjection→imagesEquiv : {f : B → C} (p : A ↠ B) → Image (f ∘ p .fst) ≃ Image f
preCompSurjection→imagesEquiv {B} {C} {A} {f} p = imagesEquiv
  (imageSurjection (f ∘ p .fst)) (imageInclusion (f ∘ p .fst))
  surj-Im-f∘e (imageInclusion f)
  refl where
  surj-Im-f∘e : A ↠ Image f
  surj-Im-f∘e = compSurjection p (imageSurjection f)

preCompEquiv→imagesEquiv : {f : B → C} (e : A ≃ B) → Image (f ∘ equivFun e) ≃ Image f
preCompEquiv→imagesEquiv {B} {C} {A} {f} e = preCompSurjection→imagesEquiv (map-snd isEquiv→isSurjection e)
