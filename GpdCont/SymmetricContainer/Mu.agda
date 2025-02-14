{-# OPTIONS --lossy-unification #-}
open import GpdCont.Prelude
open import GpdCont.SymmetricContainer.Parametrized

module GpdCont.SymmetricContainer.Mu {ℓ} {Ix : Type ℓ} (F : ContainerP⁺¹ Ix) where

open import GpdCont.SymmetricContainer.Substitution
open import GpdCont.W
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Algebra
open import GpdCont.TwoCategory.Initial

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sum using (inl ; inr)

private
  open ContainerP F

  Param : Ix → ⟨ Shape ⟩ → hSet _
  Param ix = Pos (param ix)

  Free : ⟨ Shape ⟩ → hSet _
  Free = Pos free
  {-# INLINE Free #-}

FixFree : Type _
FixFree = Fix ⟨ Shape ⟩ (⟨_⟩ ∘ Free)

FixParam : (φ : FixFree) → Ix → φ .Fix.Carrier → Type ℓ
FixParam φ ix = Fixᴰ φ $ ⟨_⟩ ∘ Param ix

isSetFixParam : (φ : FixFree) (ix : Ix) {s : φ .Fix.Carrier} → isSet (FixParam φ ix s)
isSetFixParam φ ix = isOfHLevelFixᴰ φ 2 $ str ∘ Param ix

μ-shape : hGroupoid _
μ-shape .fst = W ⟨ Shape ⟩ (⟨_⟩ ∘ Free) -- W (Σₛ 𝔹Gₛ) _
μ-shape .snd = WPath.isOfHLevelSucW 2 (str Shape)

μF : FixFree
μF .Fix.Carrier = ⟨ μ-shape ⟩
μF .Fix.fix = isoToEquiv unfoldWIso

μ-pos : (ix : Ix) → ⟨ μ-shape ⟩ → hSet ℓ
μ-pos ix s .fst = FixParam μF ix s
μ-pos ix s .snd = isSetFixParam μF ix {s}

μ : ContainerP Ix
μ .ContainerP.Shape = μ-shape
μ .ContainerP.Pos = μ-pos


private
  module FAlg = TwoCategory (Algebra (Subst F))
  module ContainerPCat = TwoCategory (ContainerPCat Ix)

private
  module μ = ContainerP μ

open MorphismP

μ-fold-pos : ∀ ix s f → ⟨ ContainerP.Pos μ ix (sup-W s f) ⟩ → ⟨ ContainerP.Pos (F [ μ ]) ix (s , f) ⟩
μ-fold-pos ix s f (here pos-ix) = inl pos-ix
μ-fold-pos ix s f (there q x) = inr (q , x)

μ-fold : MorphismP (F [ μ ]) μ
μ-fold .shape-map (s , f) = sup-W s f
μ-fold .pos-map ix (s , f) = μ-fold-pos ix s f

μ-unfold-shape : ⟨ μ.Shape ⟩ → ⟨ ContainerP.Shape (F [ μ ]) ⟩
μ-unfold-shape (sup-W s f) .fst = s
μ-unfold-shape (sup-W s f) .snd = f

μ-unfold-pos : ∀ ix w → ⟨ ContainerP.Pos (F [ μ ]) ix (μ-unfold-shape w) ⟩ → ⟨ μ.Pos ix w ⟩
μ-unfold-pos ix (sup-W s f) (inl pos-ix) = here pos-ix
μ-unfold-pos ix (sup-W s f) (inr (pos-free , μpos-free)) = there pos-free μpos-free

μ-unfold : MorphismP μ (F [ μ ])
μ-unfold .shape-map = μ-unfold-shape
μ-unfold .pos-map = μ-unfold-pos

μ-alg : FAlg.ob
μ-alg .fst = μ
μ-alg .snd = μ-fold

μ-is-initial : isInitial (Algebra (Subst {Ix = Ix} F)) μ-alg
μ-is-initial (G , g) r₁@(in₁ , (p₁ , _)) r₂@(in₂ , (p₂ , _)) = goal where
  module G = ContainerP G
  module g = MorphismP g
  module in₁ = MorphismP in₁
  module in₂ = MorphismP in₂
  _ : ContainerPCat.hom μ G
  _ = in₁

  _ : compP μ-fold in₁ ≡ compP (substr-map F in₁) g
  _ = p₁

{-
  module _ (into : MorphismP μ G) (is-alg-hom : compP μ-hom into ≡ compP (substr-map F into) g) where
    module into = MorphismP into
    shape-unfold : (w : ⟨ μ.Shape ⟩) → into.shape-map w ≡ g.shape-map (shape w , sub w ⋆ into.shape-map)
    shape-unfold (sup-W s f) i = is-alg-hom i .MorphismP.shape-map (s , f)

    pos-unfold : PathP (λ i → ∀ ix w → ⟨ G.Pos ix (shape-unfold w i) ⟩ → ⟨ ContainerP.Pos (F [ μ ]) ix (shape w , sub w) ⟩) {! !} ({! (compP (substr-map F into) g) .MorphismP.pos-map !} )
    pos-unfold i ix w@(sup-W s f) = is-alg-hom i .MorphismP.pos-map ix (s , f)

  univ₁-shape : ∀ w → in₁.shape-map w ≡ in₂.shape-map w
  univ₁-shape w@(sup-W s f) = shape-unfold in₁ p₁ w ∙∙ cong (λ f → g.shape-map (s , f)) (funExt $ univ₁-shape ∘ f) ∙∙ (sym $ shape-unfold in₂ p₂ w)
  -}

  module univ₁-shape s f (sub-path : ∀ pos → in₁.shape-map (f pos) ≡ in₂.shape-map (f pos)) where
    left = (cong shape-map p₁ ≡$ (s , f))

    center : g.shape-map (s , f ⋆ in₁.shape-map) ≡ g.shape-map (s , f ⋆ in₂.shape-map)
    center = cong (λ - → g.shape-map (s , -)) (funExt sub-path)

    right = (cong shape-map (sym p₂) ≡$ (s , f))

    ind : in₁.shape-map (sup-W s f) ≡ in₂.shape-map (sup-W s f)
    ind = left ∙∙ center ∙∙ right

    filler : PathP (λ i → left (~ i) ≡ right i) center ind
    filler = doubleCompPath-filler left center right

  univ₁-shape' : ∀ w → in₁.shape-map w ≡ in₂.shape-map w
  univ₁-shape' = WIndExplicit univ₁-shape.ind

  -- univ₁-shape'' : in₁.shape-map ≡ in₂.shape-map
  -- foo : ∀ w → g.shape-map (shape w , sub w ⋆ in₁.shape-map) ≡ g.shape-map (shape w , sub w ⋆ in₂.shape-map)

  -- univ₁-shape'' = (funExt $ shape-unfold in₁ p₁) ∙∙ funExt foo ∙∙ (sym $ funExt $ shape-unfold in₂ p₂)
  -- foo = WIndExplicit λ s f sub-path → cong (λ into → g.shape-map (s , f ⋆ into)) {! !}

  -- univ₁-shape' : in₁.shape-map ≡ in₂.shape-map
  -- univ₁-shape' = funExt λ { w@(sup-W s f) → shape-unfold in₁ p₁ w ∙∙ (λ i → g.shape-map (s , λ p → univ₁-shape' i (f p))) ∙∙ (sym $ shape-unfold in₂ p₂ w) }

  -- g-shape : (w : ⟨ μ.Shape ⟩) → g.shape-map (shape w , sub w ⋆ in₁.shape-map) ≡ g.shape-map (shape w , sub w ⋆ in₂.shape-map)
  -- g-shape w@(sup-W s f) i = g.shape-map (s , λ p → univ₁-shape' i (f p))


  -- univ₁-pos : (ix : Ix) (w : ⟨ μ.Shape ⟩) → PathP (λ i → ⟨ ContainerP.Pos G ix (univ₁-shape w i) ⟩ → ⟨ μ.Pos ix w ⟩) (in₁.pos-map ix w) (in₂.pos-map ix w)
  -- univ₁-pos ix w@(sup-W s f) = doubleCompPathP' (λ (u : ⟨ μ.Shape ⟩ → ⟨ ContainerP.Shape G ⟩) → ⟨ ContainerP.Pos G ix (u w) ⟩ → ⟨ μ.Pos ix w ⟩)
  --   {x = in₁.shape-map}
  --   {y = λ w → g.shape-map (shape w , sub w ⋆ in₁.shape-map)}
  --   {z = λ w → g.shape-map (shape w , sub w ⋆ in₂.shape-map)}
  --   {w = in₂.shape-map}
  --   (funExt (shape-unfold in₁ p₁))
  --   (funExt λ { w@(sup-W s f) → cong (λ f → g.shape-map (s , f)) (funExt $ univ₁-shape ∘ f) })
  --   (funExt (sym ∘ shape-unfold in₂ p₂))
  --   {y' = {!g.pos-map ix (s , f ⋆ in₁.shape-map) !} ⋆ in₁.pos-map ix w}
  --   {! !}
  --   {! !}
  --   {! !}

  univ₁-pos' : (ix : Ix) (w : ⟨ μ.Shape ⟩) → PathP (λ i → ⟨ G.Pos ix (univ₁-shape' w i) ⟩ → ⟨ μ.Pos ix w ⟩) (in₁.pos-map ix w) (in₂.pos-map ix w)
  univ₁-pos' ix = WIndExplicit λ s f sub-pathP → doubleCompPathP' (λ (u : ⟨ G.Shape ⟩) → ⟨ G.Pos ix u ⟩ → ⟨ μ.Pos ix (sup-W s f) ⟩)
    {x = in₁.shape-map (sup-W s f)}
    {y = g.shape-map (s , f ⋆ in₁.shape-map)}
    {z = g.shape-map (s , f ⋆ in₂.shape-map)}
    {w = in₂.shape-map (sup-W s f)}
    (cong MorphismP.shape-map p₁ ≡$ (s , f))
    (cong (λ f → g.shape-map (s , f)) $ funExt λ pos → univ₁-shape' (f pos))
    (cong MorphismP.shape-map (sym p₂) ≡$ (s , f))
    {x' = in₁.pos-map ix (sup-W s f)}
    {y' = g.pos-map ix (s , f ⋆ in₁.shape-map) ⋆ {! in₁.pos-map ix (sup-W s f) !}}
    {z' = g.pos-map ix (s , f ⋆ in₂.shape-map) ⋆ {! !}}
    {w' = in₂.pos-map ix (sup-W s f)}
    -- (λ i x → {! μ-unfold .MorphismP.pos-map ix ? (p₁ i .MorphismP.pos-map ix (s , f) x) !})
    {! !}
    {! !}
    {! !}

  univ₁-pos'' : (ix : Ix) (w : ⟨ μ.Shape ⟩) → PathP (λ i → ⟨ G.Pos ix (univ₁-shape' w i) ⟩ → ⟨ μ.Pos ix w ⟩) (in₁.pos-map ix w) (in₂.pos-map ix w)
  univ₁-pos'' ix = WIndExplicit goal where
    module _
      (s : ⟨ Shape ⟩)
      (f : ⟨ Free s ⟩ → W ⟨ Shape ⟩ (λ ix → ⟨ Free ix ⟩))
      (sub-pathP : ∀ pos → PathP (λ i → ⟨ G.Pos ix (univ₁-shape' (f pos) i) ⟩ → ⟨ μ.Pos ix (f pos) ⟩) (in₁.pos-map ix (f pos)) (in₂.pos-map ix (f pos)))
      where
        goal : PathP (λ i → ⟨ G.Pos ix (univ₁-shape' (sup-W s f) i) ⟩ → ⟨ μ.Pos ix (sup-W s f) ⟩) (in₁.pos-map ix (sup-W s f)) (in₂.pos-map ix (sup-W s f))
        goal i pos = {!comp (λ j → ⟨ G.Pos ix (univ₁-shape.filler s f sub-path i) ⟩ → ⟨ μ.Pos ix (sup-W s f) ⟩)!}

  univ₁ : in₁ ≡ in₂
  univ₁ = MorphismP≡ (funExt univ₁-shape') (funExt₂ univ₁-pos')

  univ₁-left : in₁ ≡ compP (compP μ-unfold (substr-map F in₁)) g
  univ₁-left = MorphismP≡Ext $ WIndExplicit λ where
    s f sub .fst i → p₁ i .shape-map (s , f)
    s f sub .snd ix i posᴳ → {! μ-unfold-pos ix (sup-W s f) (p₁ i .pos-map ix (s , f) posᴳ) !}

  univ₁-left' : in₁ ≡ compP (compP μ-unfold (substr-map F in₁)) g
  univ₁-left' = MorphismP≡ univ₁-left-shape (funExt₂ univ₁-left-pos) where
    univ₁-left-shape : in₁.shape-map ≡ (compP (compP μ-unfold (substr-map F in₁)) g) .shape-map
    univ₁-left-shape i (sup-W s f) = p₁ i .shape-map (s , f)

    univ₁-left-pos : ∀ ix (w : ⟨ μ.Shape ⟩) → PathP (λ i → ⟨ G.Pos ix (univ₁-left-shape i w) ⟩ → ⟨ μ.Pos ix w ⟩) (in₁.pos-map ix w) ((compP (compP μ-unfold (substr-map F in₁)) g) .pos-map ix w)
    univ₁-left-pos ix (sup-W s f) = funExtNonDep λ pos-path → {! !}

  univ₁' : in₁ ≡ in₂
  univ₁' = MorphismP≡Ext $ WIndExplicit goal where
    module _
      (s : ⟨ Shape ⟩)
      (f : ⟨ Free s ⟩ → W ⟨ Shape ⟩ (λ ix → ⟨ Free ix ⟩))
      (sub-path : (pos : ⟨ Free s ⟩) → Σ[ p ∈ in₁.shape-map (f pos) ≡ in₂.shape-map (f pos) ] (∀ ix → PathP (λ i → ⟨ G.Pos ix (p i) ⟩ → ⟨ μ-pos ix (f pos) ⟩) (in₁.pos-map ix (f pos)) (in₂.pos-map ix (f pos))))
      where

      module p* = univ₁-shape s f (fst ∘ sub-path)

      left* : ∀ ix → PathP (λ i → ⟨ G.Pos ix (p*.left i) ⟩ → ⟨ μ-pos ix (sup-W s f) ⟩) (in₁.pos-map ix (sup-W s f)) {! !}
      -- left* ix = funExtNonDep λ {p₀} {p₁} pos-path → {! sub-path p₀ !}
      left* ix i posᴳ = {! g !}

      center* : ∀ ix → PathP (λ i → ⟨ G.Pos ix (p*.center i) ⟩ → ⟨ μ-pos ix (sup-W s f) ⟩) (g.pos-map ix (s , f ⋆ in₁.shape-map) ⋆ {! !} ⋆ μ-unfold-pos ix (sup-W s f)) {! !}
      center* ix i posᴳ = {! sub-path !}

      right* : ∀ ix → PathP (λ i → ⟨ G.Pos ix (p*.right i) ⟩ → ⟨ μ-pos ix (sup-W s f) ⟩) {! !} (in₂.pos-map ix (sup-W s f))
      right* = {! !}

      goal : Σ[ p* ∈ (in₁.shape-map (sup-W s f) ≡ in₂.shape-map (sup-W s f)) ] ((ix : Ix) → PathP (λ i → ⟨ G.Pos ix (p* i) ⟩ → ⟨ μ-pos ix (sup-W s f) ⟩) (in₁.pos-map ix (sup-W s f)) (in₂.pos-map ix (sup-W s f)))
      goal .fst = p*.ind
      goal .snd ix = doubleCompPathP' (λ (u : ⟨ G.Shape ⟩) → ⟨ G.Pos ix u ⟩ → ⟨ μ.Pos ix (sup-W s f) ⟩) p*.left p*.center p*.right (left* ix) (center* ix) (right* ix)

  univ : FAlg.rel r₁ r₂
  univ .fst = univ₁
  univ .snd = {! !}

  goal : isContr (FAlg.rel r₁ r₂)
  goal .fst = univ
  goal .snd = {! !}

μ-initial : SubstInitial F
μ-initial .fst = μ-alg
μ-initial .snd = μ-is-initial
