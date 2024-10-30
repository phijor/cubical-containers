module GpdCont.Group.SymmetricGroup where

open import GpdCont.Prelude hiding (_▷_)

open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base

import Cubical.Algebra.SymmetricGroup as SymmetricGroup

𝔖 : ∀ {ℓ} (X : hSet ℓ) → Group ℓ
𝔖 (X , is-set-X) = SymmetricGroup.Symmetric-Group X is-set-X
