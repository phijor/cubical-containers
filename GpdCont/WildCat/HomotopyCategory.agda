module GpdCont.WildCat.HomotopyCategory where

open import GpdCont.Prelude

open import Cubical.WildCat.Base renaming (_[_,_] to _[_,_]ʷ)
open import Cubical.Categories.Category.Base

open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

private
  variable
    ℓo ℓh : Level

ho : WildCat ℓo ℓh → Category ℓo ℓh
ho C = def where
  module C = WildCat C

  ∥C[_,_]∥₂ : (x y : C.ob) → Type _
  ∥C[_,_]∥₂ x y = ∥ C.Hom[_,_] x y ∥₂

  isSet-∥C[-,-]∥₂ : ∀ {x y : C.ob} → isSet ∥C[ x , y ]∥₂
  isSet-∥C[-,-]∥₂ = ST.isSetSetTrunc

  def : Category _ _
  def .Category.ob = C.ob
  def .Category.Hom[_,_] x y = ∥C[ x , y ]∥₂
  def .Category.id {x} = ST.∣ C.id ∣₂
  def .Category._⋆_ = ST.rec2 isSet-∥C[-,-]∥₂ λ f g → ST.∣ f C.⋆ g ∣₂
  def .Category.⋆IdL = ST.elim (λ f → ST.isSetPathImplicit) λ f → cong ST.∣_∣₂ (C.⋆IdL f)
  def .Category.⋆IdR = ST.elim (λ f → ST.isSetPathImplicit) λ f → cong ST.∣_∣₂ (C.⋆IdR f)
  def .Category.⋆Assoc = ST.elim3 (λ f g h → ST.isSetPathImplicit) λ f g h → cong ST.∣_∣₂ (C.⋆Assoc f g h)
  def .Category.isSetHom = isSet-∥C[-,-]∥₂

module Notation (C : WildCat ℓo ℓh) where
  private module C = WildCat C

  hoHom : (c d : C.ob) → Type _
  hoHom = ho C .Category.Hom[_,_]

  trunc-hom : {c d : C.ob} → C [ c , d ]ʷ → ho C [ c , d ]
  trunc-hom = ST.∣_∣₂
