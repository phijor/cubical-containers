{-# OPTIONS --lossy-unification #-}
module GpdCont.Delooping.Functor where

open import GpdCont.Prelude

open import GpdCont.Group.MapConjugator using (Conjugator ; idConjugator ; compConjugator)
open import GpdCont.Group.TwoCategory using (TwoGroup)

open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.LaxFunctor
open import GpdCont.TwoCategory.StrictFunctor using (StrictFunctor)
open import GpdCont.TwoCategory.Pseudofunctor
open import GpdCont.TwoCategory.HomotopyGroupoid using (hGpdCat ; isLocallyGroupoidalHGpdCat)
open import GpdCont.TwoCategory.LocalCategory using (LocalCategory)
open import GpdCont.TwoCategory.StrictFunctor.LocalFunctor as LocalFunctor using (LocalFunctor)

import      GpdCont.Delooping as Delooping
open import GpdCont.Delooping.Map as Map using (map ; map≡ ; module MapPathEquiv)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws as GL using (compPathRefl)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; GroupEquiv)
open import Cubical.Algebra.Group.MorphismProperties renaming (compGroupHom to _∙Grp_ ; compGroupEquiv to _∙GrpE_)

open import Cubical.Categories.Category.Base using (CatIso ; pathToIso)
open import Cubical.Categories.Functor.Base using (Functor)
open import Cubical.Categories.Equivalence.WeakEquivalence

-- Delooping is a locally essentially surjective functor:
-- The functorial action on 1-cells has a mere section.
module LocalInverse {ℓ} {G H : Group ℓ} where
  open import Cubical.HITs.PropositionalTruncation hiding (map)
  open import Cubical.HITs.PropositionalTruncation.Monad

  private
    open module H = GroupStr (str H) using (_·_)
    module G = GroupStr (str G)

    𝔹G = Delooping.𝔹 G
    𝔹H = Delooping.𝔹 H

    module 𝔹G = Delooping G
    module 𝔹H = Delooping H

  -- Any map (f : 𝔹G → 𝔹H) is uniquely determined by the choice of
  -- a point (y : 𝔹H) and a group homomorphism (φ : G → π₁(𝔹H, y)).
  unrec-fun : (f : 𝔹G → 𝔹H) → Σ[ y ∈ 𝔹H ] GroupHom G (𝔹H.π₁ y)
  unrec-fun = invEq (𝔹G.recEquivHom {X = 𝔹H , 𝔹H.isGroupoid𝔹})

  -- We would like to define a group homomorphism G → H from (f : 𝔹G → 𝔹H)
  -- by inspecting which group elements in H correspond to paths
  --
  --    (𝔹G.loop ⋆ f) : G → π₁(𝔹H, f ⋆)
  --
  -- But (f ⋆ : 𝔹H) is *not* definitionally equal to (⋆ : 𝔹H), therefore we
  -- cannot apply the equivalence (loop : H ≃ π₁(𝔹H, ⋆)) to extract elements of H.
  --
  -- If we have access to a path (p : f ⋆ ≡ ⋆), then we can conjugate by `p`:
  -- multiplication (λ q → p⁻¹ ∙ q ∙ p) induces an equivalence of groups
  --
  --    π₁(𝔹H, f ⋆) ≃ π₁(𝔹H, ⋆),
  --
  -- and postcomposing with this equivalence, we obtain a group homomorphism
  --
  --                  φ                conj(p)             loop⁻¹
  --    unmap f : G ----> π₁(𝔹H, f ⋆) --------> π₁(𝔹H, ⋆) -------> H
  unmap : (f : 𝔹G → 𝔹H) (p : f 𝔹G.⋆ ≡ 𝔹H.⋆) → GroupHom G H
  unmap f p using (y , φ) ← unrec-fun f = φ ∙Grp (GroupEquiv→GroupHom fixit) where
    conjEquiv : GroupEquiv (𝔹H.π₁ y) (𝔹H.π₁ 𝔹H.⋆)
    conjEquiv = 𝔹H.conjugatePathEquiv p

    fixit : GroupEquiv (𝔹H.π₁ y) H
    fixit = conjEquiv ∙GrpE 𝔹H.unloopGroupEquiv

  -- For any choice of path (p : f ⋆ ≡ ⋆), we can show that this is a section of `map`.
  -- We construct the homotopy with `f` pointwise by induction on the domain.
  unmap-section : (f : 𝔹G → 𝔹H) (p : f 𝔹G.⋆ ≡ 𝔹H.⋆) → map (unmap f p) ≡ f
  unmap-section f p using (y , (φ , _)) ← unrec-fun f = funExt ext where
    -- On the point, both `map` and `unmap` compute to the point in the codomain.
    -- Thus, p⁻¹ connects `⋆` to `f ⋆`.
    ext⋆ : 𝔹H.⋆ ≡ f 𝔹G.⋆
    ext⋆ = sym p

    -- For a loop in 𝔹G defined by (g : G), we need to show that there
    -- is a filler for the square
    --
    --               cong (map (unmap f p)) (loop g)
    --        (f ⋆) --------------------------------- (f ⋆)
    --          |                                       |
    --          |                                       |
    --      p⁻¹ |                                       | p⁻¹
    --          |                                       |
    --          |                                       |
    --         (⋆) ----------------------------------- (⋆)
    --                      cong f (loop g)
    ext-loop : ∀ g → Square (sym p) (sym p) (cong (map (unmap f p)) (𝔹G.loop g)) (φ g)
    ext-loop g =
      -- We observe that both the top and bottom side of this square simplify.
      subst (λ top → Square (sym p) (sym p) top (φ g)) (top-path g) (ext-loop' g) where

      -- First, φ is defined by induction from f.
      -- The bottom of the square is (definitionally) equal to (φ g).
      _ : ∀ g → cong f (𝔹G.loop g) ≡ φ g
      _ = λ g → refl

      -- Secondly, on loops, unmap is defined as a conjugation, followed
      -- by the inverse to `loop : H → π₁(𝔹H, ⋆)`:
      conjₚ : f 𝔹G.⋆ ≡ f 𝔹G.⋆ → 𝔹H.⋆ ≡ 𝔹H.⋆
      conjₚ = sym p ∙∙_∙∙ p

      _ : ∀ g → cong (map $ unmap f p) (𝔹G.loop g) ≡ 𝔹H.loop (𝔹H.unloop (conjₚ (φ g)))
      _ = λ g → refl

      -- We thus substitute (conjₚ (φ g)) for the top path by cancelling loop and unloop, ...
      top-path : ∀ g → conjₚ (φ g) ≡ cong (map $ unmap f p) (𝔹G.loop g)
      top-path g = loop-retract $ conjₚ (φ g) where
        loop-retract : ∀ h → h ≡ 𝔹H.loop (𝔹H.unloop h)
        loop-retract h = sym (retEq 𝔹H.ΩDelooping≃ h)

      -- ...and are left to show that there's a filler for the square
      --
      --            p⁻¹ ∙∙ (φ g) ∙∙ p
      --     (f ⋆) ------------------- (f ⋆)
      --       |                         |
      --       |                         |
      --   p⁻¹ |                         | p⁻¹
      --       |                         |
      --       |                         |
      --      (⋆) --------------------- (⋆)
      --                   φ g
      --
      -- which follows from uniqueness of path composites.
      ext-loop' : ∀ g → Square (sym p) (sym p) ((sym p) ∙∙ (φ g) ∙∙ p) (φ g)
      ext-loop' g i j = doubleCompPath-filler (sym p) (φ g) p (~ j) i

    ext : ∀ x → map (unmap f p) x ≡ f x
    ext = 𝔹G.elimSet (λ x → 𝔹H.isGroupoid𝔹 _ (f x)) ext⋆ ext-loop

  conjugateSection-map : (f : 𝔹G → 𝔹H) → f 𝔹G.⋆ ≡ 𝔹H.⋆ → Σ[ φ ∈ GroupHom G H ] map φ ≡ f
  conjugateSection-map f p .fst = unmap f p
  conjugateSection-map f p .snd = unmap-section f p

  -- In general, there is a set of paths (f ⋆ ≡ ⋆) from which we would
  -- habe to pick one in order to apply `unmap f`.  This is not posible
  -- in general without choice.  But since 𝔹H is path-connected, we merely
  -- get such a path, thus merely a section to `map`.
  isSurjection-map : (f : 𝔹G → 𝔹H) → ∃[ φ ∈ GroupHom G H ] map φ ≡ f
  isSurjection-map f = do
    -- 𝔹H is path-connected, thus we merely get (p : f 𝔹G.⋆ ≡ 𝔹H.⋆)
    p ← 𝔹H.merePath (f 𝔹G.⋆) 𝔹H.⋆
    -- Conjugation by p gives us a group hom with the right endpoints
    return $ conjugateSection-map f p

module TwoFunc (ℓ : Level) where
  private
    variable
      G H K L : Group ℓ
      φ ψ ρ : GroupHom G H

    module TwoGroup = TwoCategory (TwoGroup ℓ)
    module hGpdCat = TwoCategory (hGpdCat ℓ)

  𝔹-ob : TwoGroup.ob → hGpdCat.ob
  𝔹-ob G .fst = Delooping.𝔹 G
  𝔹-ob G .snd = Delooping.isGroupoid𝔹
  {-# INJECTIVE_FOR_INFERENCE 𝔹-ob #-}

  𝔹-hom : {G H : TwoGroup.ob} → TwoGroup.hom G H → hGpdCat.hom (𝔹-ob G) (𝔹-ob H)
  𝔹-hom φ = Map.map φ
  {-# INJECTIVE_FOR_INFERENCE 𝔹-hom #-}

  module _ {G H : TwoGroup.ob}
    {φ₀₀ φ₀₁ φ₁₀ φ₁₁ : hGpdCat.hom (𝔹-ob G) (𝔹-ob H)}
    {𝔹φ₀₋ : φ₀₀ ≡ φ₀₁}
    {𝔹φ₁₋ : φ₁₀ ≡ φ₁₁}
    {𝔹φ₋₀ : φ₀₀ ≡ φ₁₀}
    {𝔹φ₋₁ : φ₀₁ ≡ φ₁₁}
    where

    private
      module 𝔹G = Delooping G
      module 𝔹H = Delooping H

    -- Squares in 𝔹H are propositions, so squares of functions 𝔹G → 𝔹H
    -- are exactly exactly squares in 𝔹H of the functions evaluated at 𝔹G.⋆.
    𝔹-hom-SquareEquiv :
      Square (𝔹φ₀₋ ≡$ 𝔹G.⋆) (𝔹φ₁₋ ≡$ 𝔹G.⋆)  (𝔹φ₋₀ ≡$ 𝔹G.⋆) (𝔹φ₋₁ ≡$ 𝔹G.⋆) ≃ Square 𝔹φ₀₋ 𝔹φ₁₋ 𝔹φ₋₀ 𝔹φ₋₁
    𝔹-hom-SquareEquiv = 𝔹G.elimPropEquiv (λ x → 𝔹H.isPropDeloopingSquare) ∙ₑ funExtSquareEquiv

    𝔹-hom-Square :
      (sq : Square (𝔹φ₀₋ ≡$ 𝔹G.⋆) (𝔹φ₁₋ ≡$ 𝔹G.⋆)  (𝔹φ₋₀ ≡$ 𝔹G.⋆) (𝔹φ₋₁ ≡$ 𝔹G.⋆))
      → Square 𝔹φ₀₋ 𝔹φ₁₋ 𝔹φ₋₀ 𝔹φ₋₁
    𝔹-hom-Square = equivFun 𝔹-hom-SquareEquiv

  𝔹-rel : {G H : TwoGroup.ob} {φ ψ : TwoGroup.hom G H} → TwoGroup.rel φ ψ → hGpdCat.rel (𝔹-hom φ) (𝔹-hom ψ)
  𝔹-rel {φ} {ψ} = map≡ φ ψ

  𝔹-rel-id : 𝔹-rel (TwoGroup.id-rel φ) ≡ refl
  𝔹-rel-id {φ} = Map.map≡-id-refl φ

  𝔹-rel-trans : (h₁ : TwoGroup.rel φ ψ) (h₂ : TwoGroup.rel ψ ρ) → 𝔹-rel (compConjugator h₁ h₂) ≡ 𝔹-rel h₁ ∙ 𝔹-rel h₂
  𝔹-rel-trans {φ} {ψ} {ρ} = Map.map≡-comp-∙ φ ψ ρ

  private
    𝔹-trans-lax : (φ : TwoGroup.hom G H) (ψ : TwoGroup.hom H K) → (𝔹-hom φ hGpdCat.∙₁ 𝔹-hom ψ) ≡ 𝔹-hom (φ TwoGroup.∙₁ ψ)
    𝔹-trans-lax {G} {H} {K} φ ψ = funExt (𝔹G.elimSet isSetMotive refl λ g i j → 𝔹K.loop ((φ TwoGroup.∙₁ ψ) .fst g) i) where
      module 𝔹G = Delooping G
      module 𝔹K = Delooping K

      isSetMotive : (x : Delooping.𝔹 G) → isSet ((𝔹-hom ψ $ 𝔹-hom φ x) ≡ (𝔹-hom (φ TwoGroup.∙₁ ψ) x))
      isSetMotive x = 𝔹K.isGroupoid𝔹 _ _

    𝔹-trans-lax-natural : {φ₁ φ₂ : TwoGroup.hom G H} {ψ₁ ψ₂ : TwoGroup.hom H K}
      → (h : TwoGroup.rel φ₁ φ₂)
      → (k : TwoGroup.rel ψ₁ ψ₂)
      → ((𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ∙ 𝔹-trans-lax φ₂ ψ₂) ≡ (𝔹-trans-lax φ₁ ψ₁ ∙ 𝔹-rel (h TwoGroup.∙ₕ k))
    𝔹-trans-lax-natural {G} {H} {K} {φ₁} {φ₂} {ψ₁} {ψ₂} h k = funExtSquare lax where
      module K = GroupStr (str K)
      module 𝔹G = Delooping G
      module 𝔹H = Delooping H
      module 𝔹K = Delooping K

      open 𝔹G using (cong⋆ ; cong⋆-∙)

      -- The meat of the proof: Horizontal composition computes to the correct loop at the point.
      -- This is almost definitional, except that the LHS computes to the diagonal of a composite square,
      -- in particular it is the diagonal that shows that the group element underlying `(h TwoGroup.∙ₕ k)`
      -- is a conjugator of ψ₁ and ψ₂.
      lemma : cong⋆ (𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ≡ 𝔹K.loop ((h TwoGroup.∙ₕ k) .fst)
      lemma = Map.map≡-loopᵝ ψ₁ ψ₂ k (h .fst)

      lax⋆ : cong⋆ (((𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ∙ 𝔹-trans-lax φ₂ ψ₂)) ≡ cong⋆ (𝔹-trans-lax φ₁ ψ₁ ∙ 𝔹-rel (h TwoGroup.∙ₕ k))
      lax⋆ =
        cong⋆ (((𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ∙ 𝔹-trans-lax φ₂ ψ₂))      ≡⟨ cong⋆-∙ (𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) (𝔹-trans-lax φ₂ ψ₂) ⟩
        cong⋆ (𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ∙ cong⋆ (𝔹-trans-lax φ₂ ψ₂)  ≡⟨⟩
        cong⋆ (𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ∙ refl                       ≡⟨ sym $ GL.rUnit _ ⟩
        cong⋆ (𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k)                              ≡⟨ lemma ⟩
        𝔹K.loop ((h TwoGroup.∙ₕ k) .fst)                                ≡⟨⟩
        cong⋆ (𝔹-rel (h TwoGroup.∙ₕ k))                                 ≡⟨ GL.lUnit _ ⟩
        refl ∙ cong⋆ (𝔹-rel (h TwoGroup.∙ₕ k))                          ≡⟨⟩
        cong⋆ (𝔹-trans-lax φ₁ ψ₁) ∙ cong⋆ (𝔹-rel (h TwoGroup.∙ₕ k))     ≡⟨ sym $ cong⋆-∙ (𝔹-trans-lax φ₁ ψ₁) (𝔹-rel (h TwoGroup.∙ₕ k)) ⟩
        cong⋆ (𝔹-trans-lax φ₁ ψ₁ ∙ 𝔹-rel (h TwoGroup.∙ₕ k)) ∎

      lax : (x : 𝔹G.𝔹) → (((𝔹-rel h hGpdCat.∙ₕ 𝔹-rel k) ∙ 𝔹-trans-lax φ₂ ψ₂) ≡$S x) ≡ (𝔹-trans-lax φ₁ ψ₁ ∙ 𝔹-rel (h TwoGroup.∙ₕ k) ≡$S x)
      lax = 𝔹G.elimProp (λ x → 𝔹K.isGroupoid𝔹 _ _ _ _) lax⋆

    𝔹-id-lax : (G : TwoGroup.ob) → hGpdCat.id-hom (𝔹-ob G) ≡ 𝔹-hom (TwoGroup.id-hom G)
    𝔹-id-lax G = sym (Map.map-id G)

    𝔹-assoc : (φ : TwoGroup.hom G H) (ψ : TwoGroup.hom H K) (ρ : TwoGroup.hom K L)
      → Square
        ((𝔹-trans-lax φ ψ hGpdCat.∙ₕ refl′ (𝔹-hom ρ)) ∙ 𝔹-trans-lax (φ TwoGroup.∙₁ ψ) ρ)
        ((refl′ (𝔹-hom φ) hGpdCat.∙ₕ 𝔹-trans-lax ψ ρ) ∙ 𝔹-trans-lax φ (ψ TwoGroup.∙₁ ρ))
        (refl′ ((𝔹-hom φ hGpdCat.∙₁ 𝔹-hom ψ) hGpdCat.∙₁ 𝔹-hom ρ))
        (cong 𝔹-hom (TwoGroup.comp-hom-assoc φ ψ ρ))
    𝔹-assoc {G} {H} {L} φ ψ ρ = funExtSquare assoc-ext where
      module 𝔹G = Delooping G
      module 𝔹L = Delooping L

      open 𝔹G using (cong⋆ ; cong⋆-∙)

      assoc-ext : (x : 𝔹G.𝔹) → Square
        ((𝔹-trans-lax φ ψ hGpdCat.∙ₕ refl′ (𝔹-hom ρ)) ∙ 𝔹-trans-lax (φ TwoGroup.∙₁ ψ) ρ ≡$ x)
        (((refl′ (𝔹-hom φ) hGpdCat.∙ₕ 𝔹-trans-lax ψ ρ) ∙ 𝔹-trans-lax φ (ψ TwoGroup.∙₁ ρ)) ≡$ x)
        refl
        (λ i → 𝔹-hom (TwoGroup.comp-hom-assoc φ ψ ρ i) x)
      assoc-ext = 𝔹G.elimProp (λ x → 𝔹L.isPropDeloopingSquare) $
        let
          p = (𝔹-trans-lax φ ψ hGpdCat.∙ₕ refl′ (𝔹-hom ρ))
          q = (𝔹-trans-lax (φ TwoGroup.∙₁ ψ) ρ)
          r = (refl′ (𝔹-hom φ) hGpdCat.∙ₕ 𝔹-trans-lax ψ ρ)
          s = (𝔹-trans-lax φ (ψ TwoGroup.∙₁ ρ))
        in
        (cong⋆ $ p ∙ q)     ≡⟨ cong⋆-∙ p q ⟩
        (cong⋆ p ∙ cong⋆ q) ≡⟨⟩
        (refl ∙ refl)       ≡⟨ sym $ cong⋆-∙ r s ⟩
        (cong⋆ $ r ∙ s)     ∎

    𝔹-unit-left : (φ : TwoGroup.hom G H)
      → Square
        ((𝔹-id-lax G hGpdCat.∙ₕ refl′ (𝔹-hom φ)) hGpdCat.∙ᵥ 𝔹-trans-lax idGroupHom φ)
        (refl′ (𝔹-hom φ))
        (hGpdCat.comp-hom-unit-left (𝔹-hom φ))
        (cong 𝔹-hom (TwoGroup.comp-hom-unit-left φ))
    𝔹-unit-left {G} {H} φ = 𝔹-hom-Square unit-left⋆ where
      module 𝔹G = Delooping G
      module 𝔹H = Delooping H

      p : (id ⟨ 𝔹-ob G ⟩) ⋆ (𝔹-hom φ) ≡ (𝔹-hom idGroupHom) ⋆ (𝔹-hom φ)
      p = 𝔹-id-lax G hGpdCat.∙ₕ refl′ (𝔹-hom φ)

      q : (𝔹-hom idGroupHom ⋆ 𝔹-hom φ) ≡ 𝔹-hom (idGroupHom TwoGroup.∙₁ φ)
      q = 𝔹-trans-lax idGroupHom φ

      unit-left⋆ : 𝔹G.cong⋆ (p ∙ q) ≡ refl′ 𝔹H.⋆
      unit-left⋆ = 𝔹G.cong⋆-∙ p q ∙ sym compPathRefl

    𝔹-unit-right : (φ : TwoGroup.hom G H)
      → Square
        ((refl′ (𝔹-hom φ) hGpdCat.∙ₕ 𝔹-id-lax H) hGpdCat.∙ᵥ 𝔹-trans-lax φ idGroupHom)
        (refl′ (𝔹-hom φ))
        (hGpdCat.comp-hom-unit-right (𝔹-hom φ))
        (cong 𝔹-hom (TwoGroup.comp-hom-unit-right φ))
    𝔹-unit-right {G} {H} φ = 𝔹-hom-Square unit-right⋆ where
      module 𝔹G = Delooping G
      module 𝔹H = Delooping H

      p = refl′ (𝔹-hom φ) hGpdCat.∙ₕ 𝔹-id-lax H
      q = 𝔹-trans-lax φ idGroupHom

      -- Both p and q reduce to refl at the point:
      unit-right⋆ : 𝔹G.cong⋆ (p ∙ q) ≡ refl′ 𝔹H.⋆
      unit-right⋆ = 𝔹G.cong⋆-∙ p q ∙ sym compPathRefl

  TwoDelooping : LaxFunctor (TwoGroup ℓ) (hGpdCat ℓ)
  TwoDelooping .LaxFunctor.F-ob = 𝔹-ob
  TwoDelooping .LaxFunctor.F-hom = 𝔹-hom
  TwoDelooping .LaxFunctor.F-rel = 𝔹-rel
  TwoDelooping .LaxFunctor.F-rel-id = 𝔹-rel-id
  TwoDelooping .LaxFunctor.F-rel-trans = 𝔹-rel-trans
  TwoDelooping .LaxFunctor.F-trans-lax = 𝔹-trans-lax
  TwoDelooping .LaxFunctor.F-trans-lax-natural = 𝔹-trans-lax-natural
  TwoDelooping .LaxFunctor.F-id-lax = 𝔹-id-lax
  TwoDelooping .LaxFunctor.F-assoc = 𝔹-assoc
  TwoDelooping .LaxFunctor.F-unit-left = 𝔹-unit-left
  TwoDelooping .LaxFunctor.F-unit-right = 𝔹-unit-right

  private
    𝔹-hom-id : (G : TwoGroup.ob) → hGpdCat.id-hom (𝔹-ob G) ≡ 𝔹-hom (TwoGroup.id-hom G)
    𝔹-hom-id G = sym (Map.map-id G)

    𝔹-hom-comp : {G H K : TwoGroup.ob} (φ : TwoGroup.hom G H) (ψ : TwoGroup.hom H K)
      → (𝔹-hom φ hGpdCat.∙₁ 𝔹-hom ψ) ≡ 𝔹-hom (φ TwoGroup.∙₁ ψ)
    𝔹-hom-comp φ ψ = sym (Map.map-comp φ ψ)

    module 𝔹-assoc {G H K L : TwoGroup.ob} (φ* @ (φ , _) : TwoGroup.hom G H) (ψ* @ (ψ , _) : TwoGroup.hom H K) (ρ* @ (ρ , _) : TwoGroup.hom K L) where
      module 𝔹G = Delooping G
      module 𝔹L = Delooping L
      assoc-hom : (𝔹-hom φ* ⋆ 𝔹-hom ψ*) ⋆ 𝔹-hom ρ* ≡ 𝔹-hom ((φ* TwoGroup.∙₁ ψ*) TwoGroup.∙₁ ρ*)
      assoc-hom = funExt (𝔹G.elimSet (λ _ → str (𝔹-ob L) _ _) refl λ g j i → 𝔹L.loop (ρ (ψ (φ g))) j)

      filler-left-lid : ((map φ* ⋆ map ψ*) ⋆ 𝔹-hom ρ*) ≡ map ((φ* TwoGroup.∙₁ ψ*) TwoGroup.∙₁ ρ*)
      filler-left-lid = funExt (𝔹G.elimSet (λ _ → str (𝔹-ob L) _ _) refl λ g j i → 𝔹L.loop (ρ (ψ (φ g))) j)

      filler-right-lid : map φ* ⋆ (map ψ* ⋆ map ρ*) ≡ map (φ* TwoGroup.∙₁ (ψ* TwoGroup.∙₁ ρ*))
      filler-right-lid = funExt (𝔹G.elimSet (λ _ → str (𝔹-ob L) _ _) refl λ g j i → 𝔹L.loop (ρ (ψ (φ g))) j)

      private
        [φ⋆ψ]⋆ρ = cong (λ - → hGpdCat._∙₁_ {x = 𝔹-ob G} - (𝔹-hom ρ*)) (𝔹-hom-comp φ* ψ*)
        φ⋆[ψ⋆ρ] = cong (λ - → hGpdCat._∙₁_ {z = 𝔹-ob L} (𝔹-hom φ*) -) (𝔹-hom-comp ψ* ρ*)

      filler-left : PathCompFiller (cong (_⋆ (𝔹-hom ρ*)) (𝔹-hom-comp φ* ψ*)) (𝔹-hom-comp (φ* TwoGroup.∙₁ ψ*) ρ*)
      filler-left .fst = filler-left-lid
      filler-left .snd = 𝔹-hom-Square (reflSquare 𝔹L.⋆)
      {-# INJECTIVE_FOR_INFERENCE filler-left #-}

      filler-right : PathCompFiller (cong ((𝔹-hom φ*) ⋆_) (𝔹-hom-comp ψ* ρ*)) (𝔹-hom-comp φ* (ψ* TwoGroup.∙₁ ρ*))
      filler-right .fst = filler-right-lid
      filler-right .snd = 𝔹-hom-Square (reflSquare 𝔹L.⋆)
      {-# INJECTIVE_FOR_INFERENCE filler-right #-}

      assoc : PathP
        (λ i → hGpdCat.comp-hom-assoc (𝔹-hom φ*) (𝔹-hom ψ*) (𝔹-hom ρ*) i ≡ 𝔹-hom (TwoGroup.comp-hom-assoc φ* ψ* ρ* i))
        filler-left-lid
        filler-right-lid
      assoc = 𝔹-hom-Square (reflSquare 𝔹L.⋆)
      {-# INJECTIVE_FOR_INFERENCE assoc #-}

    module 𝔹-unit-left {G H : TwoGroup.ob} (φ : TwoGroup.hom G H) where
      module 𝔹H = Delooping H

      filler-lid : map φ ≡ map ((TwoGroup.id-hom G) TwoGroup.∙₁ φ)
      filler-lid = cong map (sym $ TwoGroup.comp-hom-unit-left φ)

      filler : PathCompFiller (cong (_⋆ 𝔹-hom φ) (𝔹-hom-id G)) (𝔹-hom-comp (TwoGroup.id-hom G) φ)
      filler .fst = filler-lid
      filler .snd = 𝔹-hom-Square (reflSquare 𝔹H.⋆)
      {-# INJECTIVE_FOR_INFERENCE filler #-}

      unit-left : PathP (λ i → hGpdCat.comp-hom-unit-left (𝔹-hom φ) i ≡ 𝔹-hom (TwoGroup.comp-hom-unit-left φ i))
        filler-lid
        (refl′ (𝔹-hom φ))
      unit-left = 𝔹-hom-Square (reflSquare 𝔹H.⋆)

    module 𝔹-unit-right {G H : TwoGroup.ob} (φ : TwoGroup.hom G H) where
      module 𝔹H = Delooping H

      filler-lid : map φ ≡ map (φ TwoGroup.∙₁ (TwoGroup.id-hom H))
      filler-lid = cong map (sym $ TwoGroup.comp-hom-unit-right φ)

      filler : PathCompFiller (cong ((𝔹-hom φ) hGpdCat.∙₁_) (𝔹-hom-id H)) (𝔹-hom-comp φ (TwoGroup.id-hom H))
      filler .fst = filler-lid
      filler .snd = 𝔹-hom-Square (reflSquare 𝔹H.⋆)
      {-# INJECTIVE_FOR_INFERENCE filler #-}

      unit-right : PathP (λ i → hGpdCat.comp-hom-unit-right (𝔹-hom φ) i ≡ 𝔹-hom (TwoGroup.comp-hom-unit-right φ i))
        filler-lid
        (refl′ (𝔹-hom φ))
      unit-right = 𝔹-hom-Square (reflSquare 𝔹H.⋆)


  TwoDeloopingˢ : StrictFunctor (TwoGroup ℓ) (hGpdCat ℓ)
  TwoDeloopingˢ .StrictFunctor.F-ob = 𝔹-ob
  TwoDeloopingˢ .StrictFunctor.F-hom = 𝔹-hom
  TwoDeloopingˢ .StrictFunctor.F-rel = 𝔹-rel
  TwoDeloopingˢ .StrictFunctor.F-rel-id = 𝔹-rel-id
  TwoDeloopingˢ .StrictFunctor.F-rel-trans = 𝔹-rel-trans
  TwoDeloopingˢ .StrictFunctor.F-hom-comp = 𝔹-hom-comp
  TwoDeloopingˢ .StrictFunctor.F-hom-id = 𝔹-hom-id
  TwoDeloopingˢ .StrictFunctor.F-assoc-filler-left = 𝔹-assoc.filler-left
  TwoDeloopingˢ .StrictFunctor.F-assoc-filler-right = 𝔹-assoc.filler-right
  TwoDeloopingˢ .StrictFunctor.F-assoc = 𝔹-assoc.assoc
  TwoDeloopingˢ .StrictFunctor.F-unit-left-filler = 𝔹-unit-left.filler
  TwoDeloopingˢ .StrictFunctor.F-unit-left = 𝔹-unit-left.unit-left
  TwoDeloopingˢ .StrictFunctor.F-unit-right-filler = 𝔹-unit-right.filler
  TwoDeloopingˢ .StrictFunctor.F-unit-right = 𝔹-unit-right.unit-right

  private
    module TwoDeloopingˢ = StrictFunctor TwoDeloopingˢ

  isLocallyFullyFaithfulDelooping : LocalFunctor.isLocallyFullyFaithful TwoDeloopingˢ
  isLocallyFullyFaithfulDelooping G H = goal where module _ (φ ψ : TwoGroup.hom G H) where
    goal : isEquiv 𝔹-rel
    goal = equivIsEquiv (MapPathEquiv.map≡Equiv φ ψ)

  localDeloopingEmbedding : {G H : TwoGroup.ob} (φ ψ : TwoGroup.hom G H)
    → TwoGroup.rel φ ψ ≃ hGpdCat.rel (TwoDeloopingˢ.₁ φ) (TwoDeloopingˢ.₁ ψ)
  localDeloopingEmbedding = LocalFunctor.localEmbedding TwoDeloopingˢ isLocallyFullyFaithfulDelooping

  isLocallyEssentiallySurjectiveDelooping : LocalFunctor.isLocallyEssentiallySurjective TwoDeloopingˢ
  isLocallyEssentiallySurjectiveDelooping G H = goal where module _ (f : ⟨ 𝔹-ob G ⟩ → ⟨ 𝔹-ob H ⟩) where
    open import Cubical.HITs.PropositionalTruncation.Monad
    goal : ∃[ φ ∈ GroupHom G H ] CatIso (LocalCategory _ (𝔹-ob G) (𝔹-ob H)) (map φ) f
    goal = do
      (φ , section-f-mapφ) ← LocalInverse.isSurjection-map f
      ∃-intro φ $ pathToIso section-f-mapφ

  isLocallyWeakEquivalenceDelooping : LocalFunctor.isLocallyWeakEquivalence TwoDeloopingˢ
  isLocallyWeakEquivalenceDelooping G H .isWeakEquivalence.fullfaith = isLocallyFullyFaithfulDelooping G H
  isLocallyWeakEquivalenceDelooping G H .isWeakEquivalence.esssurj = isLocallyEssentiallySurjectiveDelooping G H
