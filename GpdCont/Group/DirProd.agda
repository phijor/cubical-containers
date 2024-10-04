module GpdCont.Group.DirProd where

open import GpdCont.Prelude

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)

open import Cubical.Algebra.Group.DirProd using (DirProd) public

module DirProd {ℓ} (G H : Group ℓ) where
  open IsGroupHom

  fstHom : GroupHom (DirProd G H) G
  fstHom .fst = fst
  fstHom .snd .pres· _ _ = refl
  fstHom .snd .pres1 = refl
  fstHom .snd .presinv _ = refl

  sndHom : GroupHom (DirProd G H) H
  sndHom .fst = snd
  sndHom .snd .pres· _ _ = refl
  sndHom .snd .pres1 = refl
  sndHom .snd .presinv _ = refl

  pairingHom : {K : Group ℓ} (φ : GroupHom K G) (ψ : GroupHom K H) → GroupHom K (DirProd G H)
  pairingHom φ ψ .fst = λ k → φ .fst k , ψ .fst k
  pairingHom φ ψ .snd .pres· k₁ k₂ = ≡-× (φ .snd .pres· k₁ k₂) (ψ .snd .pres· k₁ k₂)
  pairingHom φ ψ .snd .pres1 = ≡-× (φ .snd .pres1) (ψ .snd .pres1)
  pairingHom φ ψ .snd .presinv k = ≡-× (φ .snd .presinv k) (ψ .snd .presinv k)
