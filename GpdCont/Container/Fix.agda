{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import GpdCont.Prelude

module GpdCont.Container.Fix (ℓ : Level) where

open import GpdCont.Container.Base ℓ
open import GpdCont.W as W hiding (Fix)

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Unit
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma

open Cont
open Hom

Id : Cont
Id .Shape = Unit*
Id .Pos _ = Unit*

𝟙 : Cont
𝟙 .Shape = Unit*
𝟙 .Pos _ = ⊥*

_+_ : (F G : Cont) → Cont
(F + G) .Shape = F .Shape ⊎ G .Shape
(F + G) .Pos = Sum.rec (F .Pos) (G .Pos)

map-left-+ : ∀ {F G H} → Hom G H → Hom (F + G) (F + H)
map-left-+ h .on-shape = Sum.map (id _) (h .on-shape)
map-left-+ h .on-pos = Sum.elim (λ _ → id _) (h .on-pos)

_⊗_ : (F G : Cont) → Cont
(F ⊗ G) .Shape = Σ[ s ∈ F .Shape ] (F .Pos s → G .Shape)
(F ⊗ G) .Pos (s , f) = Σ[ p ∈ F .Pos s ] G .Pos (f p)

map-left-⊗ : ∀ {F G H} → Hom G H → Hom (F ⊗ G) (F ⊗ H)
map-left-⊗ h .on-shape = map-snd (h .on-shape ∘_)
map-left-⊗ h .on-pos (s , f) = map-snd (h .on-pos (f _))

𝕄 : (F : Cont) → Cont
𝕄 F .Shape = Maybe (F .Shape)
𝕄 F .Pos = Maybe.rec ⊥* (F .Pos)

map-𝕄 : ∀ {G H} → Hom G H → Hom (𝕄 G) (𝕄 H)
map-𝕄 h .on-shape = map-Maybe (h .on-shape)
map-𝕄 h .on-pos = Maybe.elim _ (id ⊥*) (h .on-pos)

module _ (F : Cont) where
  WShape : Type _
  WShape = W (F .Shape) (F .Pos)

module Fix (F : Cont) where
  Fix : Cont → Cont
  Fix G = Id + (F ⊗ G)

  μFixShape : Type ℓ
  μFixShape = WShape (𝟙 + F)

  μFixShape' : Type ℓ
  μFixShape' = Unit* {ℓ} ⊎ (Σ[ s ∈ F .Shape ] (F .Pos s → μFixShape))

  unfoldShape : μFixShape → μFixShape'
  unfoldShape (sup-W (inl tt*) x) = inl tt*
  unfoldShape (sup-W (inr s) f) = inr (s , f)
  
  foldShape : μFixShape' → μFixShape
  foldShape (inl tt*) = sup-W (inl tt*) ⊥.rec*
  foldShape (inr (s , f)) = sup-W (inr s) f

  data μFixPos' : μFixShape' → Type ℓ where
    stop : μFixPos' (inl tt*)
    next : ∀ {s : F .Shape} {f : F .Pos s → μFixShape}
      → (p : F .Pos s)
      → (q : μFixPos' (unfoldShape (f p)))
      → μFixPos' (inr (s , f))

  μFixPos : μFixShape → Type ℓ
  μFixPos = μFixPos' ∘ unfoldShape

  μFix : Cont
  μFix .Shape = μFixShape
  μFix .Pos = μFixPos

  μFixShapeIso : Iso (Shape (Fix μFix)) (Shape μFix)
  μFixShapeIso .Iso.fun = foldShape
  μFixShapeIso .Iso.inv = unfoldShape
  μFixShapeIso .Iso.sec (sup-W (inl tt*) -) = cong (sup-W _) $ funExt λ ()
  μFixShapeIso .Iso.sec (sup-W (inr s) f) = refl
  μFixShapeIso .Iso.ret (inl tt*) = refl
  μFixShapeIso .Iso.ret (inr (s , f)) = refl


  μFixPosIso : (s* : Shape (Fix μFix)) → Iso (μFixPos (foldShape s*)) (Pos (Fix μFix) s*)
  μFixPosIso (inl tt*) = stop-iso where
    stop-iso : Iso (μFixPos' (inl tt*)) Unit*
    stop-iso .Iso.fun = const tt*
    stop-iso .Iso.inv = const stop
    stop-iso .Iso.sec _ = refl
    stop-iso .Iso.ret stop = refl
  μFixPosIso (inr (s , f)) = next-iso where
    next-iso : Iso (μFixPos' (inr (s , f))) (Σ[ p ∈ F .Pos s ] μFixPos' (unfoldShape (f p)))
    next-iso .Iso.fun (next p q) = p , q
    next-iso .Iso.inv (p , q) = next p q
    next-iso .Iso.sec _ = refl
    next-iso .Iso.ret (next p q) = refl

  -- TODO: Call this fix-sup or something; rename μ-init to fold
  μFix-fold : Hom (Fix μFix) μFix
  μFix-fold .on-shape = μFixShapeIso .Iso.fun
  μFix-fold .on-pos s* = μFixPosIso s* .Iso.fun

module _ (F : Cont) where
  open Fix F

  module _ {G H : Cont} where
    mapFix : Hom G H → Hom (Fix G) (Fix H)
    mapFix f = map-left-+ (map-left-⊗ f)

  FixAlg : Type _
  FixAlg = Σ[ G ∈ Cont ] Hom (Fix G) G

  FixAlgHom : (g h : FixAlg) → Type _
  FixAlgHom (G , g) (H , h) = Σ[ m ∈ Hom G H ] g ⨟ m ≡ mapFix m ⨟ h

  FixAlgHom≡ : {g h : FixAlg} {m n : FixAlgHom g h}
    → (p : m .fst ≡ n .fst)
    → (q : PathP (λ i → (g .snd ⨟ p i) ≡ (mapFix (p i) ⨟ h .snd)) (m .snd) (n .snd))
    → m ≡ n
  FixAlgHom≡ = curry ΣPathP

  module _ (G : Cont) (g : Hom (Fix G) G) where
    μ-init-shape : (Shape μFix) → (Shape G)
    μ-init-shape (sup-W (inl tt*) ws) = g .on-shape (inl tt*)
    μ-init-shape (sup-W (inr s) f) = g .on-shape (inr (s , μ-init-shape ∘ f))

    μ-init-pos : (s : μFixShape) → Pos G (μ-init-shape s) → μFixPos s
    μ-init-pos (sup-W (inl tt*) x) _ = stop
    μ-init-pos (sup-W (inr s) f) pᴳ = uncurry next goal where
      pos : Σ[ p ∈ F .Pos s ] G .Pos (μ-init-shape (f p))
      pos = g .on-pos _ pᴳ

      goal : Σ[ p ∈ F .Pos s ] μFixPos' (unfoldShape (f p))
      goal = map-snd (μ-init-pos (f _)) pos

    μ-init : Hom μFix G
    μ-init .on-shape = μ-init-shape
    μ-init .on-pos = μ-init-pos

    μ-init-comm : μFix-fold ⨟ μ-init ≡ mapFix μ-init ⨟ g
    μ-init-comm = Hom≡ on-shape≡ (funExt on-pos≡) where
      on-shape≡ : foldShape ⋆ μ-init-shape ≡ mapFix μ-init .on-shape ⋆ g .on-shape
      on-shape≡ = funExt λ where
        (inl tt*) → refl′ (g .on-shape $ inl tt*)
        (inr (s , f)) → refl′ ((foldShape ⋆ μ-init-shape) (inr (s , f)))

      on-pos≡ : (s : μFixShape') → PathP _ _ _
      on-pos≡ (inl tt*) = refl
      on-pos≡ (inr (s , f)) = refl

    μ-init-hom : FixAlgHom (μFix , μFix-fold) (G , g)
    μ-init-hom .fst = μ-init
    μ-init-hom .snd = μ-init-comm

    μ-is-initial : isContr (FixAlgHom (μFix , μFix-fold) (G , g))
    μ-is-initial .fst = μ-init-hom
    μ-is-initial .snd (h , h-comm) = FixAlgHom≡ μ-init≡h {! !} where
      μ-init≡h-shape : ∀ x → μ-init-shape x ≡ h .on-shape x
      μ-init≡h-shape (sup-W (inl tt*) _) = sym (cong on-shape h-comm ≡$ inl tt*) ∙ {! !}
      μ-init≡h-shape (sup-W (inr s) f) = sym $ (cong on-shape h-comm ≡$ inr (s , f))
        ∙ cong (λ f → g .on-shape (inr (s , f))) (funExt λ { p → sym (μ-init≡h-shape (f p)) })

      μ-init≡h : μ-init ≡ h
      μ-init≡h = Hom≡ (funExt μ-init≡h-shape) (funExt λ { (sup-W (inl tt*) x) → {! cong on-pos h-comm ≡$ inl tt* !}
                                                        ; (sup-W (inr s) f) → {! !} })
