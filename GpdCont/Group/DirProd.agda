module GpdCont.Group.DirProd where

open import GpdCont.Prelude

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)

open import Cubical.Algebra.Group.DirProd using (DirProd) public

module DirProd {ℓ} (G H : Group ℓ) where
  fstHom : GroupHom (DirProd G H) G
  fstHom .fst = fst
  fstHom .snd .IsGroupHom.pres· _ _ = refl
  fstHom .snd .IsGroupHom.pres1 = refl
  fstHom .snd .IsGroupHom.presinv _ = refl

  sndHom : GroupHom (DirProd G H) H
  sndHom .fst = snd
  sndHom .snd .IsGroupHom.pres· _ _ = refl
  sndHom .snd .IsGroupHom.pres1 = refl
  sndHom .snd .IsGroupHom.presinv _ = refl
