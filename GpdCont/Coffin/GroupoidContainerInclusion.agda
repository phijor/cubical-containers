open import GpdCont.Prelude
open import GpdCont.Coffin.Base
open import GpdCont.SymmetricContainer.Base

module GpdCont.Coffin.GroupoidContainerInclusion {ℓ} (C : Coffin ℓ) where
private
  module C = Coffin C

Coffin→GroupoidContainer : GCont ℓ
Coffin→GroupoidContainer .GCont.Shape = C.Shape
Coffin→GroupoidContainer .GCont.Pos = C.Pos
Coffin→GroupoidContainer .GCont.is-groupoid-shape = C.is-groupoid-shape
Coffin→GroupoidContainer .GCont.is-set-pos = C.isSetPos
