module GpdCont.Bool where

open import GpdCont.Prelude

open import Cubical.Data.Bool hiding (true* ; false*)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Base

private
  variable
    ℓ ℓA : Level
    A : Bool* {ℓ} → Type ℓA

BoolSet : hSet ℓ
BoolSet .fst = Bool*
BoolSet .snd = isOfHLevelLift 2 isSetBool

pattern true* = lift true
pattern false* = lift false

bool-elim : A true* → A false* → ∀ b → A b
bool-elim x y true* = x
bool-elim x y false* = y

bool-unelim : (∀ b → A b) → A true* × A false*
bool-unelim f .fst = f true*
bool-unelim f .snd = f false*

bool-elim-Iso : Iso (A true* × A false*) (∀ b → A b)
bool-elim-Iso .Iso.fun = uncurry bool-elim
bool-elim-Iso .Iso.inv = bool-unelim
bool-elim-Iso .Iso.rightInv f i true* = f true*
bool-elim-Iso .Iso.rightInv f i false* = f false*
bool-elim-Iso .Iso.leftInv (_ , _) = refl

bool-elim-equiv : (A true* × A false*) ≃ (∀ b → A b)
bool-elim-equiv = isoToEquiv bool-elim-Iso

bool-unelim-equiv : (∀ b → A b) ≃ (A true* × A false*)
bool-unelim-equiv = isoToEquiv (invIso bool-elim-Iso)
