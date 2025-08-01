module GpdCont.StrictGroupoid.Equiv where

open import GpdCont.StrictGroupoid.Base
open import GpdCont.StrictGroupoid.Morphism

open import GpdCont.Prelude
open import GpdCont.Univalence

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)


module _ {ℓ} (G H : StrictGroupoid ℓ) where
  private
    module G = StrictGroupoidStr (str G)
    module H = StrictGroupoidStr (str H)

  isStrictGroupoidEquiv : StrictFun G H → Type _
  isStrictGroupoidEquiv (φ , _) = isEquiv φ

  StrictGroupoidEquiv : Type _
  StrictGroupoidEquiv = Σ[ σ ∈ StrictFun G H ] (isStrictGroupoidEquiv σ)

  mkStrictGroupoidEquiv : (σ : ⟨ G ⟩ ≃ ⟨ H ⟩) → StrictFunStr G H (equivFun σ) → StrictGroupoidEquiv
  mkStrictGroupoidEquiv (σ , σ-is-equiv) σ-is-strict .fst .fst = σ
  mkStrictGroupoidEquiv (σ , σ-is-equiv) σ-is-strict .fst .snd = σ-is-strict
  mkStrictGroupoidEquiv (σ , σ-is-equiv) σ-is-strict .snd = σ-is-equiv

  univalenceStrict : (G ≡ H) ≃ StrictGroupoidEquiv
  univalenceStrict =
    (G ≡ H) ≃⟨ invEquiv ΣPathP≃PathPΣ ⟩
    (Σ[ p ∈ ⟨ G ⟩ ≡ ⟨ H ⟩ ] PathP (λ i → StrictGroupoidStr (p i)) (str G) (str H)) ≃⟨ {! !} ⟩
    (Σ[ p ∈ ⟨ G ⟩ ≡ ⟨ H ⟩ ] PathP (λ i → ∥ p i ∥₂ → p i) G.pt H.pt) ≃⟨ invEquiv $ Σ-cong-equiv-fst (invEquiv univalence) ⟩
    (Σ[ σ ∈ ⟨ G ⟩ ≃ ⟨ H ⟩ ] PathP (λ i → ∥ ua σ i ∥₂ → ua σ i) G.pt H.pt) ≃⟨ Σ-cong-equiv-snd (λ σ → {! !}) ⟩
    (Σ[ σ ∈ ⟨ G ⟩ ≃ ⟨ H ⟩ ] StrictFunStr G H (equivFun σ)) ≃⟨ {! !} ⟩
    StrictGroupoidEquiv ≃∎

  uaStrict : StrictGroupoidEquiv → G ≡ H
  uaStrict = invEq univalenceStrict

  uaStrict' : StrictGroupoidEquiv → G ≡ H
  uaStrict' ((σ , σ-is-strict) , σ-is-equiv) = StrictGroupoid≡
    p
    λ { i .StrictGroupoidStr.is-groupoid → isProp→PathP (λ i → isPropIsGroupoid {A = p i}) G.is-groupoid H.is-groupoid i
      ; i .StrictGroupoidStr.pt → pt≡ i
      ; i .StrictGroupoidStr.pt-section → {! !} }
    where
      σ* : _ ≃ _
      σ* .fst = σ
      σ* .snd = σ-is-equiv

      p = ua σ*

      pt≡ : PathP (λ i → ∥ ua σ* i ∥₂ → ua σ* i) G.pt H.pt
      -- pt≡ i x = ua-gluePath (σ , σ-is-equiv) {x = G.pt (ST.map {! !} {! !})} {! !} i
      pt≡ i ST.∣ x ∣₂ = {! σ-is-strict i  !} -- ua-gluePath σ* (λ j → σ-is-strict (~ j) {! ua-unglue (invEquiv σ*) !}) i
      pt≡ i (ST.squash₂ x y p q j k) = {! !}

  uaStrict'' : StrictGroupoidEquiv → H ≡ G
  uaStrict'' ((σ , σ-is-strict) , σ-is-equiv) = StrictGroupoid≡
    (sym p)
    λ { i .StrictGroupoidStr.is-groupoid → isProp→PathP (λ i → isPropIsGroupoid {A = p (~ i)}) H.is-groupoid G.is-groupoid i
      ; i .StrictGroupoidStr.pt → pt≡ i
      ; i .StrictGroupoidStr.pt-section → {! !} }
    where
      σ* : _ ≃ _
      σ* .fst = σ
      σ* .snd = σ-is-equiv

      p : ⟨ G ⟩ ≡ ⟨ H ⟩
      p = ua σ*

      pt≡ : PathP (λ i → ∥ ua σ* (~ i) ∥₂ → ua σ* (~ i)) H.pt G.pt
      -- pt≡ i x = ua-gluePath (σ , σ-is-equiv) {x = G.pt (ST.map {! !} {! !})} {! !} i
      -- pt≡ i ST.∣ x ∣₂ = ua-gluePath σ* {x = {!ua-unglue σ* (~ i) x !}} {! !} (~ i)
      pt≡ i ST.∣ x ∣₂ = {! !} -- glue {φ = ∂ i} (λ { (i = i0) → x ; (i = i1) → x }) (ua-unglue σ* (~ i) x)
      pt≡ i (ST.squash₂ x y p q j k) = {! !}

      is-groupoid≡ : PathP (λ i → isGroupoid (p i)) G.is-groupoid H.is-groupoid
      is-groupoid≡ i = isProp→PathP (λ i → isPropIsGroupoid {A = p i}) G.is-groupoid H.is-groupoid i

      str-path : PathP (λ i → StrictGroupoidStr (p i)) (str G) (str H)
      str-path i = {! inhFibTrunc→StrictStr (is-groupoid≡ i) inh-fib !} where
        inh-fib : (x : ∥ p i ∥₂) → fiber ST.∣_∣₂ x
        -- inh-fib = ST.elim {! !} λ (x : p i) → ? -- ua-gluePath σ* {x = {! ua-ungluePath σ* !}} {! !} i , {! !}
        inh-fib x .fst = ua-glue σ* i g h where
          g : Partial (~ i) ⟨ G ⟩
          g (i = i0) = G.pt x

          h : ⟨ H ⟩ [ ~ i ↦ (λ { (i = i0) → σ (g 1=1) }) ]
          -- h = inS (σ-is-strict (~ i) {!∣ g ∣₂ !})
          h = inS (σ {! !})
        inh-fib x .snd = {! !}
