module GpdCont.WildCat.Subtype where

open import GpdCont.Prelude renaming (id to idfun)

open import Cubical.Foundations.Function using (flip) renaming (_∘_ to _∘fun_)
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.Base using (WildCat ; _[_,_])
open import Cubical.WildCat.Functor using (WildFunctor)

private
  variable
    ℓo ℓh : Level

open WildCat

record SubtypeHom {ℓ} (C : WildCat ℓo ℓh) (P : C .ob → Type ℓ) (u v : Σ[ x ∈ C .ob ] P x) : Type ℓh where
  field
    sub : C [ u .fst , v .fst ]


SubtypeCat : ∀ {ℓ} (C : WildCat ℓo ℓh) → (P : C .ob → Type ℓ) → WildCat (ℓ-max ℓo ℓ) ℓh
SubtypeCat C P .ob = Σ[ x ∈ C .ob ] P x
SubtypeCat C P .Hom[_,_] (x , _) (y , _) = C .Hom[_,_] x y
SubtypeCat C P .id = C .id
SubtypeCat C P ._⋆_ = C ._⋆_
SubtypeCat C P .⋆IdL = C .⋆IdL
SubtypeCat C P .⋆IdR = C .⋆IdR
SubtypeCat C P .⋆Assoc = C .⋆Assoc

open SubtypeHom

SubtypeCat' : ∀ {ℓ} (C : WildCat ℓo ℓh) → (P : C .ob → Type ℓ) → WildCat (ℓ-max ℓo ℓ) ℓh
SubtypeCat' C P .ob = Σ[ x ∈ C .ob ] P x
SubtypeCat' C P .Hom[_,_] = SubtypeHom C P
SubtypeCat' C P .id .sub = C .id
SubtypeCat' C P ._⋆_ f g .sub = C ._⋆_ (f .sub) (g .sub)
SubtypeCat' C P .⋆IdL f i .sub = C .⋆IdL (f .sub) i
SubtypeCat' C P .⋆IdR f i .sub = C .⋆IdR (f .sub) i
SubtypeCat' C P .⋆Assoc f g h i .sub = C .⋆Assoc (f .sub) (g .sub) (h .sub) i
