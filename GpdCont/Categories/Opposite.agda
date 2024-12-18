open import GpdCont.Prelude

open import Cubical.Categories.Category.Base

module GpdCont.Categories.Opposite {ℓ} {ℓo ℓh} {C : Category ℓo ℓh} where

import GpdCont.Categories.Products as CatProducts
import GpdCont.Categories.Coproducts as CatCoproducts

private
  module C = CatCoproducts C ℓ

  Cᵒᵖ = C ^op
  module Cᵒᵖ = CatProducts Cᵒᵖ ℓ

OpProducts : C.Coproducts → Cᵒᵖ.Products
OpProducts ⨆C K d = prod where
  module ⨆C = CatCoproducts.UniversalElement (⨆C K d)

  prod : Cᵒᵖ.Product K d
  prod .CatProducts.UniversalElement.vertex = ⨆C.vertex
  prod .CatProducts.UniversalElement.element = ⨆C.element
  prod .CatProducts.UniversalElement.universal = ⨆C.universal
