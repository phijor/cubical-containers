module GpdCont.StrictGroupoid where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Properties using (hasSection)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.PropositionalTruncation.Monad using (_>>=_ ; return)

private
  variable
    ℓ : Level
    A : Type ℓ


record StrictGroupoidStr (A : Type ℓ) : Type ℓ where
  field
    is-groupoid : isGroupoid A
    pt : ∥ A ∥₂ → A
    pt-section : section ∣_∣₂ pt

  pt-at : A → A
  pt-at a = pt ∣ a ∣₂

  mere-retract : ∀ a → ∥ pt ∣ a ∣₂ ≡ a ∥₁
  mere-retract a = ST.PathIdTrunc₀Iso .Iso.fun (pt-section ∣ a ∣₂)

unquoteDecl StrictGroupoidStrIsoΣ = declareRecordIsoΣ StrictGroupoidStrIsoΣ (quote StrictGroupoidStr)

instance
  StrictGroupoidStrToΣ : RecordToΣ (StrictGroupoidStr A)
  StrictGroupoidStrToΣ = toΣ StrictGroupoidStrIsoΣ

StrictGroupoidStr' : (A : Type ℓ) → Type ℓ
StrictGroupoidStr' A = hasSection {A = A} ∣_∣₂ × isGroupoid A

StrictGroupoid : (ℓ : Level) → Type (ℓ-suc ℓ)
StrictGroupoid ℓ = TypeWithStr ℓ StrictGroupoidStr

module _ (G : StrictGroupoid ℓ) where
  private module G = StrictGroupoidStr (str G)
  elimProp : ∀ {ℓP} {P : ⟨ G ⟩ → Type ℓP}
    → (∀ g → isProp (P g))
    → (f* : (x : ∥ ⟨ G ⟩ ∥₂) → P (G.pt x))
    → (∀ g → P g)
  elimProp {P} is-prop-P f* g = equivFun (PT.propTruncIdempotent≃ (is-prop-P g)) ∣p∣ where
    p' : P (G.pt-at g)
    p' = f* ST.∣ g ∣₂

    ∣p∣ : ∥ P g ∥₁
    ∣p∣ = do
      q ← G.mere-retract g
      return $ subst P (the (G.pt-at g ≡ g) q) p'

StrictGroupoidStr× : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB}
  → StrictGroupoidStr A
  → StrictGroupoidStr B
  → StrictGroupoidStr (A × B)
StrictGroupoidStr× {A} {B} strict-A strict-B = strict-Σ where
  module A = StrictGroupoidStr strict-A
  module B = StrictGroupoidStr strict-B

  is-groupoid-× : isGroupoid (A × B)
  is-groupoid-× = isGroupoid× A.is-groupoid B.is-groupoid

  pt : ∥ A × B ∥₂ → A × B
  pt = ST.rec→Gpd.fun is-groupoid-× pt₀ pt₀-coh where
    pt₀ : A × B → A × B
    pt₀ (a , b) .fst = A.pt-at a
    pt₀ (a , b) .snd = B.pt-at b

    pt₀-coh : ∀ x y → (p q : x ≡ y) → cong pt₀ p ≡ cong pt₀ q
    pt₀-coh (a₀ , b₀) (a₁ , b₁) p q i j .fst = A.pt (ST.squash₂ ∣ a₀ ∣₂ ∣ a₁ ∣₂ (cong (∣_∣₂ ∘ fst) p) (cong (∣_∣₂ ∘ fst) q) i j)
    pt₀-coh (a₀ , b₀) (a₁ , b₁) p q i j .snd = B.pt (ST.squash₂ ∣ b₀ ∣₂ ∣ b₁ ∣₂ (cong (∣_∣₂ ∘ snd) p) (cong (∣_∣₂ ∘ snd) q) i j)

  pt-section : section ∣_∣₂ pt
  pt-section = ST.elim (λ x → ST.isSetPathImplicit) λ where
    (a , b) → ST.PathIdTrunc₀Iso .Iso.inv $ PT.map2 ≡-× (A.mere-retract a) (B.mere-retract b)

  strict-Σ : StrictGroupoidStr _
  strict-Σ .StrictGroupoidStr.is-groupoid = is-groupoid-×
  strict-Σ .StrictGroupoidStr.pt = pt
  strict-Σ .StrictGroupoidStr.pt-section = pt-section

{-
StrictGroupoidStrΣ : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB}
  → StrictGroupoidStr A
  → (∀ a → StrictGroupoidStr (B a))
  → StrictGroupoidStr (Σ A B)
StrictGroupoidStrΣ {A} {B} strict-A strict-B = strict-Σ where
  module A = StrictGroupoidStr strict-A
  module B a = StrictGroupoidStr (strict-B a)

  is-groupoid-Σ : isGroupoid (Σ A B)
  is-groupoid-Σ = isGroupoidΣ A.is-groupoid B.is-groupoid

  pt : ∥ Σ A B ∥₂ → Σ A B
  pt = ST.rec→Gpd.fun is-groupoid-Σ pt₀ pt₀-coh where
    pt₀-fst : A → A
    pt₀-fst a = A.pt-at a

    pt₀-snd : ∀ {a} (b : B a) → ∥ A.pt ∣ a ∣₂ ≡ a ∥₁ → ∥ B (A.pt-at a) ∥₂
    pt₀-snd {a} b = PT.rec→Set ST.isSetSetTrunc b₀ b₀-2-const where
      b₀ : A.pt ∣ a ∣₂ ≡ a → ∥ B (A.pt-at a) ∥₂
      b₀ retr = ∣ subst B (sym retr) b ∣₂

      b₀-2-const : ∀ p q → b₀ p ≡ b₀ q
      b₀-2-const p q = ST.PathIdTrunc₀Iso .Iso.inv {!subst-filler B (sym p) b !}

    pt₀ : Σ A B → Σ A B
    pt₀ (a , b) .fst = pt₀-fst a
    pt₀ (a , b) .snd = B.pt _ (pt₀-snd b (A.mere-retract a))

    pt₀-coh : ∀ x y → (p q : x ≡ y) → cong pt₀ p ≡ cong pt₀ q
    pt₀-coh (a₀ , b₀) (a₁ , b₁) p q i j .fst = A.pt (ST.squash₂ ∣ a₀ ∣₂ ∣ a₁ ∣₂ (cong (∣_∣₂ ∘ fst) p) (cong (∣_∣₂ ∘ fst) q) i j)
    pt₀-coh (a₀ , b₀) (a₁ , b₁) p q i j .snd = {! !}

  strict-Σ : StrictGroupoidStr _
  strict-Σ .StrictGroupoidStr.is-groupoid = is-groupoid-Σ
  strict-Σ .StrictGroupoidStr.pt = pt
  strict-Σ .StrictGroupoidStr.pt-section = {! !}
-}

module _ (G H : StrictGroupoid ℓ) where
  private
    module G = StrictGroupoidStr (str G)
    module H = StrictGroupoidStr (str H)

  StrictFunStr : (φ : ⟨ G ⟩ → ⟨ H ⟩) → Type ℓ
  StrictFunStr φ = ST.map φ ⋆ H.pt ≡ G.pt ⋆ φ

  isSetStrictFunStr : ∀ φ → isSet (StrictFunStr φ)
  isSetStrictFunStr φ = isOfHLevelPath' 2 (isOfHLevelΠ 3 λ _ → H.is-groupoid) _ _

  StrictFun : Type ℓ
  StrictFun = Σ[ φ ∈ (⟨ G ⟩ → ⟨ H ⟩) ] StrictFunStr φ

  _#_ : StrictFun → ⟨ G ⟩ → ⟨ H ⟩
  _#_ = fst

  strict-fun-str : (φ : StrictFun) → StrictFunStr (φ #_)
  strict-fun-str = snd

  private module _ (φ ψ : StrictFun) where
    Code : Type ℓ
    Code = Σ[ p ∈ φ #_ ≡ ψ #_ ] PathP (λ i → StrictFunStr (p i)) (strict-fun-str φ) (strict-fun-str ψ)

    CodeEquiv : Code ≃ (φ ≡ ψ)
    CodeEquiv = ΣPathP≃PathPΣ

    isPropCode : isProp Code
    isPropCode (p₁ , q₁) (p₂ , q₂) = Σ≡Prop is-prop-is-strict-fun-path goal where
      is-prop-is-strict-fun-path : (p : φ #_ ≡ ψ #_) → isProp $ PathP (λ i → StrictFunStr (p i)) (strict-fun-str φ) (strict-fun-str ψ)
      is-prop-is-strict-fun-path p = isOfHLevelPathP' 1 (isSetStrictFunStr (ψ #_)) _ _

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

  isSetStrictGroupoidMap : isSet StrictFun
  isSetStrictGroupoidMap φ ψ = isOfHLevelRespectEquiv 1 (CodeEquiv φ ψ) (isPropCode φ ψ)

idStrict : (G : StrictGroupoid ℓ) → StrictFun G G
idStrict G .fst = id _
idStrict G .snd = funExt (ST.elim (λ x → isOfHLevelPath' 1 (G .snd .StrictGroupoidStr.is-groupoid _ _)) λ _ → refl)

module _ (G H K : StrictGroupoid ℓ) where
  private
    module G = StrictGroupoidStr (str G)
    module H = StrictGroupoidStr (str H)
    module K = StrictGroupoidStr (str K)

  compStrict : StrictFun G H → StrictFun H K → StrictFun G K
  compStrict (φ , is-strict-φ) (ψ , is-strict-ψ) .fst = φ ⋆ ψ
  compStrict (φ , is-strict-φ) (ψ , is-strict-ψ) .snd = goal where
    goal : ST.map (φ ⋆ ψ) ⋆ K.pt ≡ G.pt ⋆ (φ ⋆ ψ)
    goal = cong (_⋆ K.pt) (sym (ST.mapFunctorial φ ψ)) ∙∙ cong (ST.map φ ⋆_) is-strict-ψ ∙∙ cong (_⋆ ψ) is-strict-φ

module Category (ℓ : Level) where
  open import Cubical.Categories.Category.Base
  
  StrictGroupoidCat : Category (ℓ-suc ℓ) ℓ
  StrictGroupoidCat .Category.ob = StrictGroupoid ℓ
  StrictGroupoidCat .Category.Hom[_,_] = StrictFun
  StrictGroupoidCat .Category.id {x = G} = idStrict G
  StrictGroupoidCat .Category._⋆_ {x = G} {y = H} {z = K} = compStrict G H K
  StrictGroupoidCat .Category.⋆IdL = {! !}
  StrictGroupoidCat .Category.⋆IdR = {! !}
  StrictGroupoidCat .Category.⋆Assoc = {! !}
  StrictGroupoidCat .Category.isSetHom {x = G} {y = H} = isSetStrictGroupoidMap G H
