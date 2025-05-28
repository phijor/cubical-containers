module GpdCont.Group.DirProd where

open import GpdCont.Prelude
open import GpdCont.Group.Prelude

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)

open import Cubical.Algebra.Group.DirProd using (DirProd) public

infixl 5 _⊗_
_⊗_ = DirProd

module DirProd {ℓG ℓH} (G : Group ℓG) (H : Group ℓH) where
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

  pairingHom : ∀ {ℓK} {K : Group ℓK} (φ : GroupHom K G) (ψ : GroupHom K H) → GroupHom K (DirProd G H)
  pairingHom φ ψ .fst = λ k → (φ # k) , (ψ # k)
  pairingHom φ ψ .snd .pres· k₁ k₂ = ≡-× (φ .snd .pres· k₁ k₂) (ψ .snd .pres· k₁ k₂)
  pairingHom φ ψ .snd .pres1 = ≡-× (φ .snd .pres1) (ψ .snd .pres1)
  pairingHom φ ψ .snd .presinv k = ≡-× (φ .snd .presinv k) (ψ .snd .presinv k)

  mapRight : ∀ {ℓK} {K : Group ℓK} → (φ : GroupHom H K) → GroupHom (DirProd G H) (DirProd G K)
  mapRight φ .fst = map-snd (φ .fst)
  mapRight φ .snd .pres· (g , h) (g' , h') = cong (_ ,_) (φ .snd .pres· h h')
  mapRight φ .snd .pres1 = cong (_ ,_) (φ .snd .pres1)
  mapRight φ .snd .presinv (g , h) = cong (_ ,_) (φ .snd .presinv h)
