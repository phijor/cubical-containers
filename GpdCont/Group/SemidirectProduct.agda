module GpdCont.Group.SemidirectProduct where

open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group

open import GpdCont.Prelude
open import GpdCont.HomotopySet
open import GpdCont.GroupAction.Base

private
  Group→hSet : ∀ {ℓ} → (H : Group ℓ) → hSet ℓ
  Group→hSet H .fst = ⟨ H ⟩
  Group→hSet H .snd = str H .GroupStr.is-set

module _ {ℓ} (N H : Group ℓ) (φ : Action H (Group→hSet N)) where

  private
    G = ⟨ N ⟩ × ⟨ H ⟩

    module N = GroupStr (str N)
    module H = GroupStr (str H)
    module φ = Action φ

    _·_ : G → G → G
    ((n₁ , h₁) · (n₂ , h₂)) .fst = n₁ N.· (h₁ φ.▷ n₂)
    ((n₁ , h₁) · (n₂ , h₂)) .snd = h₁ H.· h₂

    1g : G
    1g .fst = N.1g
    1g .snd = H.1g

    id-right : (g : G) → g · 1g ≡ g
    id-right (n , h) = ≡-× p₁ {! !} where
      p₁ : n N.· (h φ.▷ N.1g) ≡ n
      p₁ = {! !}

    inv : G → G
    inv (n , h) .fst = invEq (φ.action (H.inv h)) (N.inv n)
    inv (n , h) .snd = H.inv h

  SemidirProd : Group ℓ
  SemidirProd .fst = G
  SemidirProd .snd .GroupStr.1g = 1g
  SemidirProd .snd .GroupStr._·_ = _·_
  SemidirProd .snd .GroupStr.inv = inv
  SemidirProd .snd .GroupStr.isGroup = makeIsGroup {! !}
    {! !}
    id-right
    {! !}
    {! !}
    {! !}

⋊-syntax : ∀ {ℓ} (N H : Group ℓ) → Action H (Group→hSet N) → Group ℓ
⋊-syntax = SemidirProd

infix 10 ⋊-syntax
syntax ⋊-syntax N H φ = N ⋊[ φ ] H
