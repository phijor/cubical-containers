module GpdCont.Image.Properties where

open import GpdCont.Prelude

open import Cubical.Displayed.Base using (UARel)

private
  variable
    ℓ : Level
    A B C D : Type ℓ

import GpdCont.Image as Image
module Map {ℓ≡f ℓ≡g : Level}
  (locally-small-B : UARel B ℓ≡f)
  (locally-small-D : UARel D ℓ≡g)
  (f : A → B) (g : C → D)
  where

  private
    module f = Image locally-small-B f
    module g = Image locally-small-D g
    module B = UARel locally-small-B
    module D = UARel locally-small-D

  map : (h : A → C) → f.Image → g.Image
  map h (f.imageRestriction a) = g.imageRestriction (h a)
  map h (f.imageQuo x y r i) = g.imageQuo (map h x) (map h y) cong-h i where
    r′ : (f.imageInclusion x) ≡ (f.imageInclusion y)
    r′ = B.≅→≡ r

    cong-h : g.imageInclusion (map h x) D.≅ g.imageInclusion (map h y)
    cong-h = D.≡→≅ λ i → {!r′ i !}
