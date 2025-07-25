module GpdCont.StrictGroupoid.Morphism where

open import GpdCont.Prelude
open import GpdCont.StrictGroupoid.Base
open import GpdCont.SetTruncation as ST using ()

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)

module _ {ℓG ℓH} (G : StrictGroupoid ℓG) (H : StrictGroupoid ℓH) where
  private
    module G = StrictGroupoidStr (str G)
    module H = StrictGroupoidStr (str H)

  StrictFunStr : (φ : ⟨ G ⟩ → ⟨ H ⟩) → Type (ℓ-max ℓG ℓH)
  StrictFunStr φ = ST.map φ ⋆ H.pt ≡ G.pt ⋆ φ

  isSetStrictFunStr : ∀ φ → isSet (StrictFunStr φ)
  isSetStrictFunStr φ = isOfHLevelPath' 2 (isOfHLevelΠ 3 λ _ → H.is-groupoid) _ _

  StrictFun : Type (ℓ-max ℓG ℓH)
  StrictFun = Σ[ φ ∈ (⟨ G ⟩ → ⟨ H ⟩) ] StrictFunStr φ


module StrictFun {ℓG ℓH} (G : StrictGroupoid ℓG) (H : StrictGroupoid ℓH) where
  _#_ : StrictFun G H → ⟨ G ⟩ → ⟨ H ⟩
  _#_ = fst

  strict-fun-str : (φ : StrictFun G H) → StrictFunStr G H (φ #_)
  strict-fun-str = snd

module _ {ℓG ℓH} (G : StrictGroupoid ℓG) (H : StrictGroupoid ℓH) where
  private
    ℓ = ℓ-max ℓG ℓH
    module G = StrictGroupoidStr (str G)
    module H = StrictGroupoidStr (str H)

  open StrictFun G H

  private module _ (φ ψ : StrictFun G H) where
    Code : Type ℓ
    Code = Σ[ p ∈ (φ #_) ≡ (ψ #_) ] PathP (λ i → StrictFunStr G H (p i)) (strict-fun-str φ) (strict-fun-str ψ)

    CodeEquiv : Code ≃ (φ ≡ ψ)
    CodeEquiv = ΣPathP≃PathPΣ

    isPropCode : isProp Code
    isPropCode (p₁ , q₁) (p₂ , q₂) = Σ≡Prop is-prop-is-strict-fun-path goal where
      is-prop-is-strict-fun-path : (p : φ #_ ≡ ψ #_) → isProp $ PathP (λ i → StrictFunStr G H (p i)) (strict-fun-str φ) (strict-fun-str ψ)
      is-prop-is-strict-fun-path p = isOfHLevelPathP' 1 (isSetStrictFunStr G H (ψ #_)) _ _
      
      -- Let (p₁ p₂ : φ #_ ≡ ψ #_).  To show that there is always an identification p₁ ≡ p₂, it suffices
      -- to give an identification over the points of G, i.e.
      --
      --    pointwise : cong (_ ∘ G.pt) p₁ ≡ cong (_ ∘ G.pt) p₂
      --
      -- Why? The goal is given by function extensionality of squares of functions G → H.
      -- But squares in the codomain are propositions (as H is a groupoid), hence it is enough
      -- to build the square on points of G (that is, ∥ G ∥₂).
      goal : p₁ ≡ p₂
      goal = funExtSquare $ elimProp G (λ g → isGroupoid→isPropSquare H.is-groupoid) $ funExtSquare⁻ pointwise where
        -- Denote by g* and h* the pre- and postcomposition with points of G and H, respectively:
        g* : (⟨ G ⟩ → ⟨ H ⟩) → (∥ ⟨ G ⟩ ∥₂ → ⟨ H ⟩)
        g* ρ = ρ ∘ G.pt

        h* : (⟨ G ⟩ → ⟨ H ⟩) → (∥ ⟨ G ⟩ ∥₂ → ⟨ H ⟩)
        h* ρ = H.pt ∘ ST.map ρ

        -- `pointwise` is build from the composition of three squares.
        -- The first two are q₁ and q₂, i.e. the evidence that p₁ and p₂ are
        -- identifications of point-preserving maps:
        _ : Square _ _ (cong h* p₁) (cong g* p₁)
        _ = q₁
        _ : Square _ _ (cong h* p₂) (cong g* p₂)
        _ = q₂

        -- The third square is obtained by noticing that h* factors through a set:
        --
        --                  h*
        --    (G → H) ------------> (∥ G ∥₂ → H)
        --       |                        ^
        --   map |                        | H.pt ∘_
        --       |                        |
        --       '--> (∥ G ∥₂ → ∥ H ∥₂) --'
        --
        -- ... therefore collapses paths:
        base : cong h* p₁ ≡ cong h* p₂
        base i j = H.pt ∘ trunc-base i j where
          trunc-base : Square {A = ∥ ⟨ G ⟩ ∥₂ → ∥ ⟨ H ⟩ ∥₂} (cong ST.map p₁) (cong ST.map p₂) refl refl
          trunc-base = funExtSquare λ _ → ST.isSetSetTrunc _ _ _ _

        -- Finally, we compose the three squares as follows:
        --     g* φ -------(g* p₁)------- g* ψ
        --       |  \        q₁         /  |
        --       |   \                 /   |
        --       |  h* φ --(h* p₂)-- h* ψ  |
        --       |    |               |    |
        --       |    |     base      |    |
        --       |    |               |    |
        --       |  h* φ --(h* p₁)-- h* ψ  |
        --       |   /                 \   |
        --       |  /        q₂         \  |
        --     g* φ -------(g* p₁)------- g* ψ
        pointwise : cong g* p₁ ≡ cong g* p₂
        pointwise i j = hcomp sides (base i j) where
          sides : (k : I) → Partial (∂² i j) (∥ ⟨ G ⟩ ∥₂ → ⟨ H ⟩)
          sides k (i = i0) = q₁ j k
          sides k (i = i1) = q₂ j k
          sides k (j = i0) = strict-fun-str φ k
          sides k (j = i1) = strict-fun-str ψ k

  isSetStrictFun : isSet (StrictFun G H)
  isSetStrictFun φ ψ = isOfHLevelRespectEquiv 1 (CodeEquiv φ ψ) (isPropCode φ ψ)

  StrictFun≡ : {φ ψ : StrictFun G H} → Code φ ψ → φ ≡ ψ
  StrictFun≡ = equivFun (CodeEquiv _ _)

  StrictFun≡' : {φ ψ : StrictFun G H}
    → (p : (φ #_) ≡ (ψ #_))
    → (q : (g : ⟨ G ⟩)
      → Square {A = ⟨ H ⟩}
        (φ .snd ≡$ ∣ g ∣₂)
        (ψ .snd ≡$ ∣ g ∣₂)
        (λ i → H.pt (ST.map (p i) ∣ g ∣₂))
        (p ≡$ G.pt ∣ g ∣₂)
      )
    → φ ≡ ψ
  StrictFun≡' {φ} {ψ} p q = StrictFun≡ (p , q*) where
    q* : PathP (λ i → StrictFunStr G H (p i)) (strict-fun-str φ) (strict-fun-str ψ)
    q* = funExtSquare (ST.elim (λ x → isProp→isSet (isGroupoid→isPropSquare H.is-groupoid)) q)

private
  variable
    ℓ ℓG ℓH : Level
    G H : StrictGroupoid ℓ

StrictFunPathP : (G : StrictGroupoid ℓ) (H : I → StrictGroupoid ℓ)
  → {φ₀ : StrictFun G (H i0)}
  → {φ₁ : StrictFun G (H i1)}
  → (p : PathP (λ i → ⟨ G ⟩ → ⟨ H i ⟩) (φ₀ .fst) (φ₁ .fst))
  → (q : PathP (λ i → StrictFunStr G (H i) (p i)) (φ₀ .snd) (φ₁ .snd))
  → PathP (λ i → StrictFun G (H i)) φ₀ φ₁
StrictFunPathP G H p q i .fst = p i
StrictFunPathP G H p q i .snd = q i

idStrict : (G : StrictGroupoid ℓ) → StrictFun G G
idStrict G .fst = id _
idStrict G .snd = funExt (ST.elim (λ x → isOfHLevelPath' 1 (G .snd .StrictGroupoidStr.is-groupoid _ _)) λ _ → refl)

module _ {ℓG ℓH ℓK} (G : StrictGroupoid ℓG) (H : StrictGroupoid ℓH) (K : StrictGroupoid ℓK) where
  private
    module G = StrictGroupoidStr (str G)
    module H = StrictGroupoidStr (str H)
    module K = StrictGroupoidStr (str K)

  compStrict' : StrictFun G H → StrictFun H K → StrictFun G K
  compStrict' (φ , is-strict-φ) (ψ , is-strict-ψ) .fst = φ ⋆ ψ
  compStrict' (φ , is-strict-φ) (ψ , is-strict-ψ) .snd = goal where
    goal : ST.map (φ ⋆ ψ) ⋆ K.pt ≡ G.pt ⋆ (φ ⋆ ψ)
    goal = cong (_⋆ K.pt) (sym (ST.setTruncMapComp φ ψ)) ∙∙ cong (ST.map φ ⋆_) is-strict-ψ ∙∙ cong (_⋆ ψ) is-strict-φ

  compStrict : StrictFun G H → StrictFun H K → StrictFun G K
  compStrict (φ , is-strict-φ) (ψ , is-strict-ψ) .fst = φ ⋆ ψ
  compStrict (φ , is-strict-φ) (ψ , is-strict-ψ) .snd = goal where
    goal : ST.map (φ ⋆ ψ) ⋆ K.pt ≡ G.pt ⋆ (φ ⋆ ψ)
    goal = funExt $ ST.elim
      (λ x → K.is-groupoid ((ST.map (φ ⋆ ψ) ⋆ K.pt) x) ((G.pt ⋆ φ ⋆ ψ) x))
      (λ g → (is-strict-ψ ≡$ ST.map φ ∣ g ∣₂) ∙ cong ψ (is-strict-φ ≡$ ∣ g ∣₂))

