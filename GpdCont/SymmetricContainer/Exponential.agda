open import GpdCont.Prelude
open import GpdCont.HomotopySet
open import GpdCont.HLevels

module GpdCont.SymmetricContainer.Exponential (ℓ : Level) where

open import GpdCont.TwoCategory.Base
open import GpdCont.SymmetricContainer.Base
open import GpdCont.SymmetricContainer.Morphism
import      GpdCont.SymmetricContainer.TwoCategory
open import GpdCont.TwoCategory.LocalCategory using (LocalCategory)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Functions.FunExtEquiv
import      Cubical.Data.Empty as Empty
open import Cubical.Data.Maybe
open import Cubical.Data.Sum
open import Cubical.Data.Sigma as Sigma using (ΣPathP)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base as NT using (_≅ᶜ_)
open import Cubical.Categories.Equivalence.AdjointEquivalence using (AdjointEquivalence)

private
  MaybeSet : (A : hSet ℓ) → hSet ℓ
  MaybeSet (A , is-set-A) .fst = Maybe A
  MaybeSet (A , is-set-A) .snd = isOfHLevelMaybe 0 is-set-A

  ford : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB}
    → (x : A)
    → (f : (y : A) → x ≡ y → B y)
    → B x
  ford x f = f x refl

  drop-left : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB}
    → A ⊎ B
    → Maybe B
  drop-left (inl a) = nothing
  drop-left (inr b) = just b

  extract-left : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB}
    → (x : A ⊎ B)
    → (is-left : drop-left x ≡ nothing)
    → A
  extract-left (inl a) is-left = a
  extract-left (inr x) is-left = Empty.rec (¬just≡nothing is-left)

module SymmCont where
  private SymmCont = (GpdCont.SymmetricContainer.TwoCategory.SymmContCat ℓ)
  open TwoCategory SymmCont public

  [_,_] : (F G : ob) → Category _ _
  [_,_] = LocalCategory SymmCont

  -- module ₀ (F : ob) where
  --   Shape : hGroupoid ℓ
  --   Shape = {! F!}
  --
_⊗_ : (F G : SymmCont.ob) → SymmCont.ob
F ⊗ G = mkSymmetricContainer (×OfHLevel 3 F.ShapeGroupoid G.ShapeGroupoid) (λ { (s , t) → F.PosSet s ⊎Set G.PosSet t }) where
  module F = SymmetricContainer F
  module G = SymmetricContainer G

_⇒'_ : (F G : SymmCont.ob) → SymmCont.ob
F ⇒' G = F⇒G where
  module F = SymmetricContainer F
  module G = SymmetricContainer G

  Shape : hGroupoid ℓ
  Shape .fst = Σ[ u ∈ (F.Shape → G.Shape) ] ((s : F.Shape) → G.Pos (u s) → Maybe (F.Pos s))
  Shape .snd = isGroupoidΣ
    (isGroupoidΠ (λ _ → G.is-groupoid-shape))
    (λ u → isSet→isGroupoid (isSetΠ2 (λ s _ → isOfHLevelMaybe 0 (F.is-set-pos s))))

  Pos : ⟨ Shape ⟩ → hSet ℓ
  Pos (u , f) .fst = ∥ Σ[ s ∈ F.Shape ] fiber (f s) nothing ∥₂
  Pos (u , f) .snd = ST.isSetSetTrunc

  F⇒G : SymmCont.ob
  F⇒G = mkSymmetricContainer Shape Pos

_⇒_ : (F G : SymmCont.ob) → SymmCont.ob
F ⇒ G = F⇒G where
  module F = SymmetricContainer F
  module G = SymmetricContainer G

  Shape : hGroupoid ℓ
  Shape .fst =
    Σ[ u ∈ (F.Shape → G.Shape) ]
    Σ[ f ∈ ((s : F.Shape) → G.Pos (u s) → Maybe (F.Pos s)) ]
    isSet (Σ[ s ∈ F.Shape ] (fiber (f s) nothing))
  Shape .snd = isGroupoidΣ
    (isGroupoidΠ (λ _ → G.is-groupoid-shape))
    (λ u → isSet→isGroupoid $ isSetΣSndProp
      (isSetΠ2 (λ s _ → isOfHLevelMaybe 0 (F.is-set-pos s)))
      (λ _ → isPropIsSet)
    )

  Pos : ⟨ Shape ⟩ → hSet ℓ
  Pos (u , f , fib-f) .fst = Σ[ s ∈ F.Shape ] fiber (f s) nothing
  Pos (u , f , fib-f) .snd = fib-f

  F⇒G : SymmCont.ob
  F⇒G = mkSymmetricContainer Shape Pos

eval : {F G : SymmCont.ob} → SymmCont.hom (F ⊗ (F ⇒ G)) G
eval {F} {G} = hom where
  module F = SymmetricContainer F
  module G = SymmetricContainer G

  shape : F.Shape × (F ⇒ G) .SymmetricContainer.Shape → G.Shape
  shape (s , u , _) = u s

  pos : ∀ s* → G.Pos (shape s*) → (F.Pos (s* .fst)) ⊎ (Σ[ s ∈ F.Shape ] fiber (s* .snd .snd .fst s) nothing)
  pos (s , u , f , fib-f) q = ford (f s q) eval-pos-helper where
    eval-pos-helper : (y : Maybe (F.Pos s)) → f s q ≡ y → F.Pos s ⊎ (Σ[ s ∈ F.Shape ] fiber (f s) nothing)
    eval-pos-helper nothing eq = inr (s , q , eq)
    eval-pos-helper (just p) _ = inl p

  hom : SymmCont.hom _ _
  hom .Morphism.shape-map = shape
  hom .Morphism.pos-map = pos

eval' : {F G : SymmCont.ob} → SymmCont.hom (F ⊗ (F ⇒' G)) G
eval' {F} {G} = hom where
  module F = SymmetricContainer F
  module G = SymmetricContainer G

  shape : F.Shape × (F ⇒' G) .SymmetricContainer.Shape → G.Shape
  shape (s , u , _) = u s

  pos : ∀ s* → G.Pos (shape s*) → (F.Pos (s* .fst)) ⊎ ∥ Σ[ s ∈ F.Shape ] fiber (s* .snd .snd s) nothing ∥₂
  pos (s , u , f) q = ford (f s q) eval'-pos-helper where
    eval'-pos-helper : (y : Maybe (F.Pos s)) → f s q ≡ y → F.Pos s ⊎ ∥ Σ[ s ∈ F.Shape ] fiber (f s) nothing ∥₂
    eval'-pos-helper nothing eq = inr ST.∣ s , q , eq ∣₂
    eval'-pos-helper (just p) _ = inl p

  hom : SymmCont.hom _ _
  hom .Morphism.shape-map = shape
  hom .Morphism.pos-map = pos

mkLocalFunctor : {X Y A B : SymmCont.ob}
  → (SymmCont.hom X Y → SymmCont.hom A B)
  → Functor SymmCont.[ X , Y ] SymmCont.[ A , B ]
mkLocalFunctor f .Functor.F-ob = f
mkLocalFunctor f .Functor.F-hom = cong f
mkLocalFunctor f .Functor.F-id = refl
mkLocalFunctor f .Functor.F-seq = cong-∙ f

module _ (X F G : SymmCont.ob) where
  private
    module F = SymmetricContainer F
    module G = SymmetricContainer G
    module X = SymmetricContainer X

  uncurryHom : SymmCont.hom X (F ⇒ G) → SymmCont.hom (X ⊗ F) G
  uncurryHom α = def where
    module α = Morphism α

    shape : X.Shape × F.Shape → G.Shape
    shape (sx , sf) = α.shape-map sx .fst sf

    pos : ∀ s* → G.Pos (shape s*) → X.Pos (s* .fst) ⊎ F.Pos (s* .snd)
    pos (sx , sf) q = ford (α.shape-map sx .snd .fst sf q) uncurry-pos-helper where
      uncurry-pos-helper : (y : Maybe (F.Pos sf)) → α.shape-map sx .snd .fst sf q ≡ y → X.Pos sx ⊎ F.Pos sf
      uncurry-pos-helper nothing eq = inl (α.pos-map sx (sf , q , eq))
      uncurry-pos-helper (just pf) eq = inr pf

    def : Morphism _ _
    def .Morphism.shape-map = shape
    def .Morphism.pos-map = pos

  uncurryHom' : SymmCont.hom X (F ⇒' G) → SymmCont.hom (X ⊗ F) G
  uncurryHom' α = uncurry-def where
    module α = Morphism α

    shape : X.Shape × F.Shape → G.Shape
    shape (sx , sf) = α.shape-map sx .fst sf

    -- αₛ : ∀ s* → G.Pos (shape s*) → Maybe (F.Pos (s* .snd))
    -- αₛ (sx , sf) q = α.shape-map sx .snd sf q

    -- pos' : ∀ sx sf → singl (αₛ (sx , sf) {! !}) → X.Pos sx ⊎ F.Pos sf
    -- pos' sx sf = {! !}

    pos : ∀ s* → G.Pos (shape s*) → X.Pos (s* .fst) ⊎ F.Pos (s* .snd)
    pos (sx , sf) q = ford (α.shape-map sx .snd sf q) uncurry-pos-helper where
      uncurry-pos-helper : (y : Maybe (F.Pos sf)) → α.shape-map sx .snd sf q ≡ y → X.Pos sx ⊎ F.Pos sf
      uncurry-pos-helper nothing eq = inl (α.pos-map sx ST.∣ sf , q , eq ∣₂)
      uncurry-pos-helper (just pf) eq = inr pf

    uncurry-def : Morphism _ _
    uncurry-def .Morphism.shape-map = shape
    uncurry-def .Morphism.pos-map = pos

  curryHom : SymmCont.hom (X ⊗ F) G → SymmCont.hom X (F ⇒ G)
  curryHom α = def where
    module α = Morphism α

    shape : X.Shape → SymmetricContainer.Shape (F ⇒ G)
    shape sx .fst = curry α.shape-map sx
    shape sx .snd .fst sf q = drop-left $ α.pos-map (sx , sf) q
    shape sx .snd .snd = is-set where
      is-set : isSet (Σ[ sf ∈ F.Shape ] Σ[ q ∈ G.Pos (α.shape-map (sx , sf)) ] drop-left (α.pos-map (sx , sf) q) ≡ nothing)
      is-set = {! !}

    pos : (sx : X.Shape) → SymmetricContainer.Pos (F ⇒ G) (shape sx) → X.Pos sx
    pos sx (sf , q , ≡nothing) = extract-left either ≡nothing where
      either : X.Pos sx ⊎ F.Pos sf
      either = α.pos-map (sx , sf) q

    def : Morphism _ _
    def .Morphism.shape-map = shape
    def .Morphism.pos-map = pos

  curryHom' : SymmCont.hom (X ⊗ F) G → SymmCont.hom X (F ⇒' G)
  curryHom' α = curry-def where
    module α = Morphism α

    shape : X.Shape → SymmetricContainer.Shape (F ⇒' G)
    shape sx .fst = curry α.shape-map sx
    shape sx .snd sf q = drop-left $ α.pos-map (sx , sf) q

    pos : (sx : X.Shape) → SymmetricContainer.Pos (F ⇒' G) (shape sx) → X.Pos sx
    pos sx = ST.rec (X.is-set-pos sx) λ { (sf , q , ≡nothing) → extract-left (α.pos-map (sx , sf) q) ≡nothing }

    curry-def : Morphism _ _
    curry-def .Morphism.shape-map = shape
    curry-def .Morphism.pos-map = pos

  curryEquiv : AdjointEquivalence SymmCont.[ X , F ⇒ G ] SymmCont.[ X ⊗ F , G ]
  curryEquiv .AdjointEquivalence.fun = mkLocalFunctor uncurryHom
  curryEquiv .AdjointEquivalence.inv = mkLocalFunctor curryHom
  curryEquiv .AdjointEquivalence.η = {! !}
  curryEquiv .AdjointEquivalence.ε = {! !}
  curryEquiv .AdjointEquivalence.triangleIdentities = {! !}

  curryFun' = mkLocalFunctor curryHom'
  uncurryFun' = mkLocalFunctor uncurryHom'

  curry-uncurry : (α : SymmCont.hom X (F ⇒' G)) → curryHom' (uncurryHom' α) ≡ α
  curry-uncurry α = Morphism≡ (funExt λ sx → ΣPathP (refl , funExt₂ λ sf q → {! α.shape-map sx .snd sf q!})) {! !}
    where
      module α = Morphism α

  curry-η : 𝟙⟨ SymmCont.[ X , F ⇒' G ] ⟩ NT.⇒ curryFun' ∘F uncurryFun'
  curry-η .NT.NatTrans.N-ob f = sym (curry-uncurry f)
  curry-η .NT.NatTrans.N-hom = {! !}

  curry-η-iso : 𝟙⟨ SymmCont.[ X , F ⇒' G ] ⟩ ≅ᶜ curryFun' ∘F uncurryFun'
  curry-η-iso .NT.NatIso.trans = curry-η
  curry-η-iso .NT.NatIso.nIso = {! !}

  curryEquiv' : AdjointEquivalence SymmCont.[ X , F ⇒' G ] SymmCont.[ X ⊗ F , G ]
  curryEquiv' .AdjointEquivalence.fun = mkLocalFunctor uncurryHom'
  curryEquiv' .AdjointEquivalence.inv = mkLocalFunctor curryHom'
  curryEquiv' .AdjointEquivalence.η = {! !}
  curryEquiv' .AdjointEquivalence.ε = {! !}
  curryEquiv' .AdjointEquivalence.triangleIdentities = {! !}
