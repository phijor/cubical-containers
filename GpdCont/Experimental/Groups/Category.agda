module GpdCont.Experimental.Groups.Category where

open import GpdCont.Prelude hiding (id ; _⋆_)
open import GpdCont.Experimental.Groups.Base
open import GpdCont.Experimental.Groups.Homomorphism as GroupHom using (GroupHom)

open import Cubical.WildCat.Base

open WildCat

GroupCategory : (ℓ : Level) → WildCat _ _
GroupCategory ℓ .ob = Group ℓ
GroupCategory ℓ .Hom[_,_] = GroupHom
GroupCategory ℓ .id {x = G} = GroupHom.id G
GroupCategory ℓ ._⋆_ = GroupHom.comp
GroupCategory ℓ .⋆IdL = GroupHom.compIdL
GroupCategory ℓ .⋆IdR = GroupHom.compIdR
GroupCategory ℓ .⋆Assoc = GroupHom.compAssoc
