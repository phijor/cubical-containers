open import GpdCont.Prelude

module GpdCont.Categories.Sets (ℓ : Level) where

open import GpdCont.HomotopySet

open import Cubical.Foundations.Equiv using (equivIsEquiv)
open import Cubical.Data.Sigma using (curryEquiv)
import      Cubical.Categories.Instances.Sets as SetCat
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable

SET = SetCat.SET ℓ

open import GpdCont.Categories.Products SET ℓ
open import GpdCont.Categories.Coproducts SET ℓ

module _ (K : hSet ℓ) (A : ⟨ K ⟩ → hSet ℓ) where
  SetProduct : Product K A
  SetProduct .UniversalElement.vertex = ΠSet {S = ⟨ K ⟩} A
  SetProduct .UniversalElement.element k φ = φ k
  SetProduct .UniversalElement.universal B = equivIsEquiv flipEquiv

SetProducts : Products
SetProducts = SetProduct

module _ (K : hSet ℓ) (A : ⟨ K ⟩ → hSet ℓ) where
  SetCoproduct : Coproduct K A
  SetCoproduct .UniversalElement.vertex = ΣSet K A
  SetCoproduct .UniversalElement.element k a = k , a
  SetCoproduct .UniversalElement.universal B = equivIsEquiv curryEquiv

SetCoproducts : Coproducts
SetCoproducts = SetCoproduct
