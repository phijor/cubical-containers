module GpdCont.Categories.Exponential where

open import GpdCont.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct

open Category

module _ {ℓo ℓh} (C : Category ℓo ℓh) (s t : C .ob) (bp-s : ∀ x → BinProduct C x s) where
  open module _×y (x : C .ob) = BinProduct (bp-s x) renaming (binProdOb to _×s)

  record Exponential : Type _ where
    field
      exponentialOb : C .ob
      exponentialEv : C [ exponentialOb ×s , t ]
      exponentialUniv : ∀ {z} (e : C [ z ×s , t ]) → ∃![ u ∈ C [ z , exponentialOb ] ]  ?
