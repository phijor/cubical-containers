module GpdCont.PropositionalTruncation where

open import GpdCont.Prelude

open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  variable
    ℓ : Level
    A B : Type ℓ

propTruncIso : Iso A B → Iso ∥ A ∥₁ ∥ B ∥₁
propTruncIso is = ∥is∥ where
  open Iso
  ∥is∥ : Iso _ _
  ∥is∥ .fun = PT.map (is .fun)
  ∥is∥ .inv = PT.map (is .inv)
  ∥is∥ .rightInv _ = PT.isPropPropTrunc _ _
  ∥is∥ .leftInv _ = PT.isPropPropTrunc _ _
