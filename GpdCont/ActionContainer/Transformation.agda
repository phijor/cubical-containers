{-# OPTIONS --lossy-unification #-}
open import GpdCont.Prelude
open import GpdCont.ActionContainer.Abstract
import GpdCont.ActionContainer.Morphism as ActionContainerMorphism

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels as HLevels using (isSetΣ)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport using (subst⁻ ; subst⁻-filler)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base

module GpdCont.ActionContainer.Transformation {ℓ} {C D : ActionContainer ℓ} where

private
  open module C = ActionContainer C using ()
    renaming
      ( Shape to S
      ; Pos to P
      ; Symm to G
      ; action to σ
      )
  module G {s : S} = GroupStr (C.symm-group-str s)

  open module D = ActionContainer D using ()
    renaming
      ( Shape to T
      ; Pos to Q
      ; Symm to H
      ; isSetSymm to isSetH
      ; action to τ
      )
  module H {t : T} = GroupStr (D.symm-group-str t)

  open ActionContainerMorphism C D

module _ (u : S → T) (F F′ : Morphismᴰ u) where
  open Morphismᴰ F using () renaming (pos-map to f ; symm-map to φ)
  open Morphismᴰ F′ using () renaming (pos-map to f′ ; symm-map to φ′)

  record Transformationᴰ : Type ℓ where
    field
      conjugator : (s : S) → H (u s)
      is-conjugate : ∀ s (g : G s) → (φ s g) H.· (conjugator s) ≡ (conjugator s) H.· (φ′ s g)
      is-pos-equiv : ∀ s → f s ≡ f′ s ∘ equivFun (τ (conjugator s))

open Transformationᴰ

module _ {u : S → T} {F F′ : Morphismᴰ u} where
  open Morphismᴰ F using () renaming (pos-map to f ; symm-map to φ)
  open Morphismᴰ F′ using () renaming (pos-map to f′ ; symm-map to φ′)

  TransformationᴰPath : ∀ {αᴰ βᴰ : Transformationᴰ u F F′} → αᴰ .conjugator ≡ βᴰ .conjugator → αᴰ ≡ βᴰ
  TransformationᴰPath p i .conjugator = p i
  TransformationᴰPath {αᴰ} {βᴰ} p i .is-conjugate s g = isProp→PathP {B = λ i → (φ _ g H.· p i s) ≡ (p i s H.· φ′ _ g)} (λ i → isSetH _ _ _)
    (αᴰ .is-conjugate s g)
    (βᴰ .is-conjugate s g)
    i
  TransformationᴰPath {αᴰ} {βᴰ} p i .is-pos-equiv s = isProp→PathP {B = λ i → f s ≡ f′ s ∘ equivFun (τ (p i s))}
    (λ i → HLevels.isOfHLevelPath' 1 (HLevels.isSet→ (C.is-set-pos _)) _ _)
    (αᴰ .is-pos-equiv s)
    (βᴰ .is-pos-equiv s)
    i

idTransformationᴰ : {u : S → T} (F : Morphismᴰ u) → Transformationᴰ u F F
idTransformationᴰ {u} F = def where
  open Morphismᴰ F using () renaming (pos-map to f ; symm-map to φ)
  def : Transformationᴰ u F F
  def .conjugator s = H.1g {u s}
  def .is-conjugate s g =
    φ _ g H.· H.1g ≡⟨ H.·IdR _ ⟩
    φ _ g ≡⟨ sym $ H.·IdL _ ⟩
    H.1g H.· φ _ g ∎
  def .is-pos-equiv s =
    f s ≡⟨⟩
    f s ∘ equivFun (idEquiv _) ≡⟨ sym $ cong (λ h → f s ∘ equivFun h) (D.action-pres-1 {u s}) ⟩
    f s ∘ equivFun (τ H.1g) ∎

vcompTransformationᴰ : {u : S → T} {F₀ F₁ F₂ : Morphismᴰ u}
  → Transformationᴰ u F₀ F₁
  → Transformationᴰ u F₁ F₂
  → Transformationᴰ u F₀ F₂
vcompTransformationᴰ {u} {F₀} {F₁} {F₂} α β = def where
  module F₀ = Morphismᴰ F₀
  module F₁ = Morphismᴰ F₁
  module F₂ = Morphismᴰ F₂
  module α = Transformationᴰ α
  module β = Transformationᴰ β

  def : Transformationᴰ u _ _
  def .conjugator s = α.conjugator s H.· β.conjugator s
  def .is-conjugate = {! !}
  def .is-pos-equiv = {! !}
  
data Transformation : (F F′ : Morphism) → Type ℓ where
  refl-shape :
    ∀ (u : S → T)
    → (F F′ : Morphismᴰ u)
    → (α : Transformationᴰ u F F′)
    → Transformation (u ▷[ F ]) (u ▷[ F′ ])

-- module TransformationPᴰMod {u u′ : S → T} (shape-path : u ≡ u′) (F : Morphismᴰ u) (F′ : Morphismᴰ u′) where
--   private
--     open module F = Morphismᴰ F using () renaming (pos-map to f ; symm-map to φ)
--     open module F′ = Morphismᴰ F′ using () renaming (pos-map to f′ ; symm-map to φ′)

--   record TransformationPᴰ : Type ℓ where
--     constructor mkTransformationP
--     field
--       {conjugator₀} : (s : S) → H (u s)
--       {conjugator₁} : (s : S) → H (u′ s)
--       conjugator-path : PathP (λ i → ∀ s → H (shape-path i s)) conjugator₀ conjugator₁
--       is-conjugate : ∀ s (g : G s) → PathP (λ i → D.Symm (shape-path i s)) (φ g D.· conjugator₀ s) (conjugator₁ s D.· φ′ g)
--       is-pos-equiv : ∀ s → PathP (λ i → ua (τ (conjugator-path i s)) i → P s) (f s) (f′ s)

module _ (F F′ : Morphism) where
  private
    open module F = Morphism F using () renaming (shape-map to u ; pos-map to f ; symm-map to φ)
    open module F′ = Morphism F′ using () renaming (shape-map to u′ ; pos-map to f′ ; symm-map to φ′)

  record TransformationP : Type ℓ where
    constructor mkTransformationP
    field
      shape-path : u ≡ u′
      {conjugator₀} : (s : S) → H (u s)
      {conjugator₁} : (s : S) → H (u′ s)
      conjugator-path : PathP (λ i → ∀ s → H (shape-path i s)) conjugator₀ conjugator₁
      is-conjugate : ∀ s (g : G s) → PathP (λ i → D.Symm (shape-path i s)) (φ _ g D.· conjugator₀ s) (conjugator₁ s D.· φ′ _ g)
      is-pos-equiv : ∀ s → PathP (λ i → ua (τ (conjugator-path i s)) i → P s) (f s) (f′ s)

  unquoteDecl TransformationPIsoΣ = declareRecordIsoΣ TransformationPIsoΣ (quote TransformationP)

  open TransformationP

  opaque
    TransformationPPath : {α β : TransformationP}
      → (conjugator₀-path : α .conjugator₀ ≡ β .conjugator₀)
      → (conjugator₁-path : α .conjugator₁ ≡ β .conjugator₁)
      → α ≡ β
    TransformationPPath {α} {β} conjugator₀-path conjugator₁-path = path where
      shape-square : α .shape-path ≡ β .shape-path
      shape-square = (HLevels.isSet→ D.is-set-shape) u u′ (α .shape-path) (β .shape-path)

      conjugator-square : SquareP (λ i j → ∀ s → H (shape-square i j s)) (α .conjugator-path) (β .conjugator-path) conjugator₀-path conjugator₁-path
      conjugator-square = HLevels.isSet→SquareP (λ i j → HLevels.isSetΠ λ s → isSetH (shape-square i j s)) _ _ _ _

      is-conjugate-square : ∀ s (g : G s) → SquareP (λ i j → H (shape-square i j s))
        (α .is-conjugate s g)
        (β .is-conjugate s g)
        (λ i → φ _ g D.· (conjugator₀-path i s))
        (λ i → conjugator₁-path i s D.· (φ′ _ g))
      is-conjugate-square s g = HLevels.isSet→SquareP (λ i j → isSetH (shape-square i j s)) _ _ _ _

      is-pos-equiv-square : ∀ s → SquareP (λ i j → ua (τ (conjugator-square i j s)) j → P s)
        (α .is-pos-equiv s)
        (β .is-pos-equiv s)
        (refl {x = f s})
        (refl {x = f′ s})
      is-pos-equiv-square s = HLevels.isSet→SquareP (λ i j → HLevels.isSet→ (C.is-set-pos s)) _ _ _ _

      path : α ≡ β
      path i .shape-path = shape-square i
      path i .conjugator₀ = conjugator₀-path i
      path i .conjugator₁ = conjugator₁-path i
      path i .conjugator-path = conjugator-square i
      path i .is-conjugate s g j = is-conjugate-square s g i j
      path i .is-pos-equiv s j = is-pos-equiv-square s i j

  TransformationPPath₀ : {α β : TransformationP}
    → (conjugator₀-path : α .conjugator₀ ≡ β .conjugator₀)
    → α ≡ β
  TransformationPPath₀ {α} {β} conjugator₀-path = TransformationPPath conjugator₀-path conjugator₁-path where
    shape-square : α .shape-path ≡ β .shape-path
    shape-square = (HLevels.isSet→ D.is-set-shape) u u′ (α .shape-path) (β .shape-path)

    conjugator₁-path : α .conjugator₁ ≡ β .conjugator₁
    conjugator₁-path = doubleCompPathP (λ i j → ∀ s → H (shape-square j i s))
      (α .conjugator-path)
      conjugator₀-path
      (β .conjugator-path)

instance
  TransformationPToΣ : {F F′ : Morphism} → RecordToΣ (TransformationP F F′)
  TransformationPToΣ {F} {F′} = toΣ (TransformationPIsoΣ F F′)

opaque
  isSetTransformationP : ∀ {F F′} → isSet (TransformationP F F′)
  isSetTransformationP = recordIsOfHLevel 2 $
    isSetΣ (isProp→isSet {! !})
    λ shape-path → isSetΣ {! !}
    λ h₀ → isSetΣ {! !}
    λ h₁ → {! !}

module TransformationPElim (F : Morphism) where
  private
    open module F = Morphism F using () renaming (mor-str to Fᴰ ; shape-map to u ; pos-map to f ; symm-map to φ)

  Motive : ∀ u′ → (u-path : u ≡ u′) → Type _
  Motive u′ shape-path =
    ∀ (F′ᴰ : Morphismᴰ u′)
    (open Morphismᴰ F′ᴰ using () renaming (pos-map to f′ ; symm-map to φ′))
    (let F′ = u′ ▷[ F′ᴰ ])
    --
    → (conjugator₀ : (s : S) → H (u s))
    → (conjugator₁ : (s : S) → H (u′ s))
    → (conjugator-path : PathP (λ i → ∀ s → H (shape-path i s)) conjugator₀ conjugator₁)
    → (is-conjugate : ∀ s (g : G s) → PathP (λ i → D.Symm (shape-path i s)) (φ _ g D.· conjugator₀ s) (conjugator₁ s D.· φ′ _ g))
    → (is-pos-equiv : ∀ s → PathP (λ i → ua (τ (conjugator-path i s)) i → P s) (f s) (f′ s))
    → Transformation F F′

  motive-reflᴰ : ∀ {F′ᴰ} {h₀} {h₁}
    (open Morphismᴰ F′ᴰ using () renaming (pos-map to f′ ; symm-map to φ′))
    → (h-path : h₀ ≡ h₁)
    → (h-conj : ∀ s (g : G s) → φ _ g D.· h₀ s ≡ h₁ s D.· φ′ _ g)
    → (h-pos-equiv : ∀ s → PathP (λ i → ua (τ (h-path i s)) i → P s) (f s) (f′ s))
    → Transformationᴰ u Fᴰ F′ᴰ
  motive-reflᴰ {h₀} h-path h-conj h-pos-equiv = λ where
    .Transformationᴰ.conjugator → h₀
    .Transformationᴰ.is-conjugate s g → h-conj s g ∙ cong (λ h → h s D.· _) (sym h-path)
    .Transformationᴰ.is-pos-equiv s i p → ua→⁻ (h-pos-equiv s) p i

  motive-refl : Motive u refl
  motive-refl F′ᴰ h₀ h₁ h-path h-conj h-pos-equiv = refl-shape u Fᴰ F′ᴰ $ motive-reflᴰ h-path h-conj h-pos-equiv

  elim : ∀ {u′} (p : u ≡ u′) → Motive u′ p
  elim = J Motive motive-refl

  elim-refl : elim refl ≡ motive-refl
  elim-refl = JRefl Motive motive-refl

  elim-refl-ext : ∀ {F′ᴰ} {conjugator} (is-conjugate : ∀ s (g : G s) → _) (is-pos-equiv : ∀ s → _)
    → elim refl F′ᴰ conjugator conjugator refl is-conjugate is-pos-equiv ≡ refl-shape u Fᴰ F′ᴰ (motive-reflᴰ refl is-conjugate is-pos-equiv)
  elim-refl-ext {F′ᴰ} {conjugator} is-conjugate is-pos-equiv i = elim-refl i F′ᴰ conjugator conjugator refl is-conjugate is-pos-equiv

TransformationP→Transformation : {F F′ : Morphism} → TransformationP F F′ → Transformation F F′
TransformationP→Transformation {F} {F′} = goal where
  open TransformationPElim F using (elim)

  goal : TransformationP F F′ → Transformation F F′
  goal (mkTransformationP shape-path conjugator-path is-conjugate is-pos-equiv)
    = elim shape-path (Morphism.mor-str F′) _ _ conjugator-path is-conjugate is-pos-equiv

Transformation→TransformationP : {F F′ : Morphism} → Transformation F F′ → TransformationP F F′
Transformation→TransformationP (refl-shape u F F′ α) = αP where
  αP : TransformationP _ _
  αP .TransformationP.shape-path = refl {x = u}
  αP .TransformationP.conjugator₀ = α .conjugator
  αP .TransformationP.conjugator₁ = α .conjugator
  αP .TransformationP.conjugator-path = refl {x = α .conjugator}
  αP .TransformationP.is-conjugate = α .is-conjugate
  αP .TransformationP.is-pos-equiv s = ua→ (funExt⁻ $ α .is-pos-equiv s)

TransformationP-Transformation-Iso : ∀ {F F′ : Morphism} → Iso (TransformationP F F′) (Transformation F F′)
TransformationP-Transformation-Iso .Iso.fun = TransformationP→Transformation
TransformationP-Transformation-Iso .Iso.inv = Transformation→TransformationP
TransformationP-Transformation-Iso {F = .(u ▷[ F ])} {F′ = .(u ▷[ F′ ])} .Iso.rightInv (refl-shape u F F′ α) =
  elim-refl-ext (α .is-conjugate) (λ s → ua→ $ funExt⁻ $ α .is-pos-equiv s) ∙ cong (refl-shape u F F′) (TransformationᴰPath refl)
  where
    open TransformationPElim (u ▷[ F ]) using (elim-refl ; elim-refl-ext)
TransformationP-Transformation-Iso .Iso.leftInv αᴾ = {! !}
  -- TransformationPPath _ _ {! !} {! !}
  --

idTransformationP : ∀ F₀ → TransformationP F₀ F₀
idTransformationP F₀ = def where
  open TransformationP

  def : TransformationP _ _
  def .shape-path = refl
  def .conjugator₀ s = D.symm-id
  def .conjugator₁ s = D.symm-id
  def .conjugator-path = refl
  def .is-conjugate s g = H.·IdR _ ∙ (sym $ H.·IdL _)
  def .is-pos-equiv s = ua→ λ p → cong (F₀ .Morphism.pos-map s) {! !}

vcompTransformationP : {F₀ F₁ F₂ : Morphism}
  → TransformationP F₀ F₁
  → TransformationP F₁ F₂
  → TransformationP F₀ F₂
vcompTransformationP {F₀} {F₁} {F₂} α β = def where
  open TransformationP

  open Morphism F₀ using () renaming (shape-map to u₀ ; symm-map to φ₀)
  open Morphism F₁ using () renaming (shape-map to u₁)
  open Morphism F₂ using () renaming (shape-map to u₂ ; symm-map to φ₂)


  h : ∀ s → H (u₁ s)
  h s = α .conjugator₁ s H.· β .conjugator₀ s

  u₀₁-ext : ∀ s → u₀ s ≡ u₁ s
  u₀₁-ext = funExt⁻ (α .shape-path)

  u₁₂-ext : ∀ s → u₁ s ≡ u₂ s
  u₁₂-ext = funExt⁻ (β .shape-path)

  h₀ : ∀ s → H (u₀ s)
  h₀ s = subst⁻ H (u₀₁-ext s) $ h s

  h₁ : ∀ s → H (u₂ s)
  h₁ s = subst H (u₁₂-ext s) $ h s

  def : TransformationP _ _
  def .shape-path = α .shape-path ∙∙ refl ∙∙ β .shape-path
  def .conjugator₀ = h₀
  def .conjugator₁ = h₁
  def .conjugator-path i s = comp Hₛ sides base  where
    Hₛ : (j : I) → Type _
    Hₛ j = H (doubleCompPath-filler (u₀₁-ext s) refl (u₁₂-ext s) j i)

    base : H (F₁ .Morphism.shape-map s)
    base = h s

    sides : (j : I) → Partial (i ∨ ~ i) (Hₛ j)
    sides j (i = i0) = subst⁻-filler H (u₀₁-ext s) (h s) j
    sides j (i = i1) = subst-filler  H (u₁₂-ext s) (h s) j
  def .is-conjugate s g = goal where

    goal : PathP (λ i → H (def .shape-path i s)) (φ₀ s g D.· h₀ s) (h₁ s D.· φ₂ s g)
    goal i = comp Hₛ sides (h s) where
      Hₛ : (j : I) → Type _
      Hₛ j = H (doubleCompPath-filler (u₀₁-ext s) refl (u₁₂-ext s) j i)

      sides : (j : I) → Partial (i ∨ ~ i) (Hₛ j)
      sides j (i = i0) = {! α .is-conjugate s g!}
      sides j (i = i1) = {! !}
  def .is-pos-equiv s = {! !}


-- foo : ∀ {F F′} → (TransformationP F F′) ≃ (Transformation F F′)
-- foo {F} {F′} = goal where
--   open Morphism F using ()
--     renaming
--       ( shape-map to u
--       ; pos-map to f
--       ; is-equivariant-pos-map to is-equivariant-f
--       ; symm-map to φ
--       ; symm-hom to φ-hom
--       )
--   open Morphism F′ using ()
--     renaming
--       ( shape-map to u′
--       ; pos-map to f′
--       ; is-equivariant-pos-map to is-equivariant-f′
--       ; symm-map to φ′
--       ; symm-hom to φ′-hom
--       )

--   goal =
--     (TransformationP F F′)
--       ≃⟨ (TransformationP F F′) ≃Σ ⟩
--     ( Σ[ p ∈ (u ≡ u′) ]
--       Σ[ h₀ ∈ (∀ s → H (u s)) ]
--       Σ[ h₁ ∈ (∀ s → H (u′ s)) ]
--       Σ[ conj-h ∈ (PathP (λ i → ∀ s → H (p i s)) h₀ h₁) ]
--       (∀ s (g : G s) → PathP (λ i → H (p i s)) (φ _ g D.· h₀ s) (h₁ s D.· φ′ _ g))
--         ×
--       (∀ s → PathP (λ i → ua (τ (conj-h i s)) i → P s) (f s) (f′ s))
--     )
--       ≃⟨ {! !} ⟩
--     (Transformation F F′)
--       ≃∎
