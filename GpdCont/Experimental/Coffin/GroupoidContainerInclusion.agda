open import GpdCont.Prelude
open import GpdCont.Experimental.Coffin.Base
open import GpdCont.SymmetricContainer.Base

module GpdCont.Experimental.Coffin.GroupoidContainerInclusion {ℓ} (C : Coffin ℓ) where
private
  module C = Coffin C

Coffin→GroupoidContainer : SymmetricContainer ℓ
Coffin→GroupoidContainer .SymmetricContainer.Shape = C.Shape
Coffin→GroupoidContainer .SymmetricContainer.Pos = C.Pos
Coffin→GroupoidContainer .SymmetricContainer.is-groupoid-shape = C.is-groupoid-shape
Coffin→GroupoidContainer .SymmetricContainer.is-set-pos = C.isSetPos
