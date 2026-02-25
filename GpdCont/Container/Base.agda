open import GpdCont.Prelude

module GpdCont.Container.Base (ℓ : Level) where

open import GpdCont.Equiv
open import GpdCont.Univalence

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (hasSection ; hasRetract)
open import Cubical.Foundations.Equiv.PathSplit using (PathSplitEquiv)
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using (compPath→Square ; Square→compPath)
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

record Cont : Type (ℓ-suc ℓ) where
  field
    Shape : Type ℓ
    Pos : Shape → Type ℓ

open Cont

Cont≡ : ∀ {F G : Cont}
  → (p : F .Shape ≡ G .Shape)
  → (q : PathP (λ i → p i → Type ℓ) (F .Pos) (G .Pos))
  → F ≡ G
Cont≡ p q i .Shape = p i
Cont≡ p q i .Pos = q i

record Hom (F G : Cont) : Type ℓ where
  field
    on-shape : F .Shape → G .Shape
    on-pos : ∀ s → G .Pos (on-shape s) → F .Pos s

unquoteDecl HomIsoΣ = declareRecordIsoΣ HomIsoΣ (quote Hom)

instance
  HomToΣ : ∀ {F G : Cont} → RecordToΣ (Hom F G)
  HomToΣ = toΣ HomIsoΣ

open Hom

isContEquiv : ∀ {F G} → Hom F G → Type _
isContEquiv f = isEquiv (f .on-shape) × ∀ s → isEquiv (f .on-pos s)

ContEquiv : (F G : Cont) → Type ℓ
ContEquiv F G = Σ[ e ∈ Hom F G ] isContEquiv e

module ContEquiv {F G} (e : ContEquiv F G) where
  on-shape≃ : F .Shape ≃ G .Shape
  on-shape≃ .fst = e .fst .on-shape
  on-shape≃ .snd = e .snd .fst

  on-pos≃ : ∀ s → G .Pos (e .fst .on-shape s) ≃ F .Pos s
  on-pos≃ s .fst = e .fst .on-pos s
  on-pos≃ s .snd = e .snd .snd s

Hom≡ : ∀ {F G} {f g : Hom F G}
  → (p : f .on-shape ≡ g .on-shape)
  → (q : PathP (λ i → ∀ s → G .Pos (p i s) → F .Pos s) (f .on-pos) (g .on-pos))
  → f ≡ g
Hom≡ p q i .on-shape = p i
Hom≡ p q i .on-pos = q i

_⨟_ : ∀ {F G H : Cont} → (f : Hom F G) → (g : Hom G H) → Hom F H
(f ⨟ g) .on-shape = f .on-shape ⋆ g .on-shape
(f ⨟ g) .on-pos _ = f .on-pos _ ∘ g .on-pos _

⟦_⟧ : (F : Cont) → Type ℓ → Type ℓ
⟦ F ⟧ X = Σ[ s ∈ F .Shape ] (F .Pos s → X)

map-⟦_⟧ : ∀ {F G : Cont} (f : Hom F G) → ∀ X → ⟦ F ⟧ X → ⟦ G ⟧ X
map-⟦ f ⟧ X (s , v) .fst = f .on-shape s
map-⟦ f ⟧ X (s , v) .snd = f .on-pos s ⋆ v

map-ext : ∀ {F : Cont} {X Y} (f : X → Y) → ⟦ F ⟧ X → ⟦ F ⟧ Y
map-ext f (s , v) .fst = s
map-ext f (s , v) .snd = v ⋆ f

isNat : (F G : Cont) → (∀ X → ⟦ F ⟧ X → ⟦ G ⟧ X) → Type (ℓ-suc ℓ)
isNat F G α = ∀ X Y (g : X → Y) → α X ⋆ map-ext g ≡ map-ext g ⋆ α Y

Nat : (F G : Cont) → Type (ℓ-suc ℓ)
Nat F G = Σ[ α ∈ (∀ X → ⟦ F ⟧ X → ⟦ G ⟧ X) ] isNat F G α

map-⟦_⟧-nat : ∀ {F G : Cont} (f : Hom F G) → Nat F G
map-⟦ f ⟧-nat .fst = map-⟦ f ⟧
map-⟦ f ⟧-nat .snd _ _ _ = refl

mkHomExt : ∀ {F G : Cont}
  → (∀ s → ⟦ G ⟧ (F .Pos s))
  → Hom F G
mkHomExt fs .on-shape = fst ∘ fs
mkHomExt fs .on-pos = snd ∘ fs

unmap-⟦_⟧ : ∀ {F G : Cont} → (∀ X → ⟦ F ⟧ X → ⟦ G ⟧ X) → Hom F G
unmap-⟦_⟧ {F} {G} α = mkHomExt α[id] where
  α' : (s : F .Shape) → (X : Type ℓ) → (F .Pos s → X) → ⟦ G ⟧ X
  α' s X f = α X (s , f)

  α[id] : (s : F .Shape) → ⟦ G ⟧ (F .Pos s)
  α[id] s = α' s (F .Pos s) (id $ F .Pos s)

ShapeUnitEquiv : (F : Cont) → ⟦ F ⟧ Unit* ≃ Shape F
ShapeUnitEquiv F = Σ-contractSnd λ s → isContrΠ λ _ → isContrUnit*

{-
unmap-⟦_⟧' : ∀ {F G : Cont} → (∀ X → ⟦ F ⟧ X → ⟦ G ⟧ X) → Hom F G
unmap-⟦_⟧' {F} {G} α = hom where
  α₁ : ⟦ F ⟧ Unit* → ⟦ G ⟧ Unit*
  α₁ = α Unit*

  module _ (s : F .Shape) where
    αᴾ : ⟦ F ⟧ (F .Pos s) → ⟦ G ⟧ (F .Pos s)
    αᴾ = α (F .Pos s)

    αᴾ[id] : ⟦ F ⟧ (F .Pos s) → ⟦ G ⟧ (F .Pos s)
    _ = {! αᴾ !}

  u : F .Shape → G .Shape
  u = invEq (ShapeUnitEquiv F) ⋆ α₁ ⋆ equivFun (ShapeUnitEquiv G)

  frob : ∀ s → G .Pos (u s) → G .Pos (α (F .Pos s) (s , id _) .fst)
  frob s = {! !}

  f : ∀ s → G .Pos (u s) → F .Pos s
  f s = frob s ⋆ αᴾ s (s , id _) .snd

  hom : Hom F G
  hom .on-shape = u
  hom .on-pos = f
-}

record isUniv {ℓ} (P : Type ℓ → Type ℓ) : Type (ℓ-suc ℓ) where
  field
    is-prop : {A : Type ℓ} → isProp (P A)
    is-sub-Σ : {A : Type ℓ} {B : A → Type ℓ} → P A → (∀ a → P (B a)) → P (Σ A B)
    is-sub-→ : {A : Type ℓ} {B : Type ℓ} → P B → P (A → B)
    -- is-sub-≡ : {A : Type ℓ} → P A → (x y : A) → P (x ≡ y)
    -- is-sub-Π : {A : Type ℓ} {B : A → Type ℓ} → (∀ a → P (B a)) → P (∀ a → B a)

  Ty = TypeWithStr ℓ P

module Sub
  (P : Type ℓ → Type ℓ)
  (is-univ-P : isUniv P)
  -- (H : Type ℓ → Type ℓ)
  -- (is-prop-H : {A : Type _} → isProp (H A))
  -- (η : ∀ {A} → A → H A)
  where
  private
    module P = isUniv is-univ-P

  -- Assuming that positions are P as well is necessary to define unmap-⟦_⟧ᴾ
  SubCont : Type (ℓ-suc ℓ)
  SubCont = Σ[ F ∈ Cont ] P (F .Shape) × (∀ s → P (F .Pos s))

  Shapeᴾ : SubCont → P.Ty
  Shapeᴾ (F , is-P-shape , _) .fst = F .Shape
  Shapeᴾ (F , is-P-shape , _) .snd = is-P-shape

  Posᴾ : (F : SubCont) → (s : ⟨ Shapeᴾ F ⟩) → P.Ty
  Posᴾ (F , _ , is-P-pos) s .fst = F .Pos s
  Posᴾ (F , _ , is-P-pos) s .snd = is-P-pos s

  SubHom : (F G : SubCont) → Type _
  SubHom (F , _) (G , _) = Hom F G

  isSub-⟦_⟧ : (F : SubCont) (X : P.Ty) → P $ ⟦ F .fst ⟧ ⟨ X ⟩
  isSub-⟦ F , is-P-shape , _ ⟧ (X , is-P-X) = P.is-sub-Σ is-P-shape λ s → P.is-sub-→ is-P-X

  ⟦_⟧ᴾ : SubCont → (P.Ty → P.Ty)
  ⟦ F , _ ⟧ᴾ (X , is-P) .fst = ⟦ F ⟧ X
  ⟦ F ⟧ᴾ X .snd = isSub-⟦ F ⟧ X

  module Map (F G : SubCont) where
    private
      F[_] = map-ext {F = F .fst}
      G[_] = map-ext {F = G .fst}

    isSubNat : ((X : P.Ty) → ⟨ ⟦ F ⟧ᴾ X ⟩ → ⟨ ⟦ G ⟧ᴾ X ⟩) → Type (ℓ-suc ℓ)
    isSubNat α = (X Y : P.Ty) → (g : ⟨ X ⟩ → ⟨ Y ⟩) → α X ⋆ G[ g ] ≡ F[ g ] ⋆ α Y

    -- isSubNat' : ((X : P.Ty) → ⟨ ⟦ F ⟧ᴾ X ⟩ → ⟨ ⟦ G ⟧ᴾ X ⟩) → Type (ℓ-suc ℓ)
    -- isSubNat' α = (X Y : P.Ty) → (g : ⟨ X ⟩ → ⟨ Y ⟩) → H (α X ⋆ map-ext g ≡ map-ext g ⋆ α Y)

    SubNat : Type (ℓ-suc ℓ)
    SubNat = Σ[ α ∈ (∀ X → ⟨ ⟦ F ⟧ᴾ X ⟩ → ⟨ ⟦ G ⟧ᴾ X ⟩) ] isSubNat α

    -- SubNat' : Type (ℓ-suc ℓ)
    -- SubNat' = Σ[ α ∈ (∀ X → ⟨ ⟦ F ⟧ᴾ X ⟩ → ⟨ ⟦ G ⟧ᴾ X ⟩) ] isSubNat' α

    map-⟦_⟧ᴾ : (f : SubHom F G) → SubNat
    map-⟦ f ⟧ᴾ .fst (X , _) = map-⟦ f ⟧ X
    map-⟦ f ⟧ᴾ .snd X Y g = refl

    -- map-⟦_⟧ᴾ' : (f : SubHom F G) → SubNat'
    -- map-⟦ f ⟧ᴾ' .fst (X , _) = map-⟦ f ⟧ X
    -- map-⟦ f ⟧ᴾ' .snd X Y g = η refl

    private
      unmap-⟦_⟧-impl : (α : ((X : P.Ty) → ⟨ ⟦ F ⟧ᴾ X ⟩ → ⟨ ⟦ G ⟧ᴾ X ⟩)) → SubHom F G
      unmap-⟦_⟧-impl α = mkHomExt λ s → α (Posᴾ F s) (s , id ⟨ Posᴾ F s ⟩)

    unmap-⟦_⟧ᴾ : (α : SubNat) → SubHom F G
    unmap-⟦_⟧ᴾ (α , _) = unmap-⟦ α ⟧-impl

    -- unmap-⟦_⟧ᴾ' : (α : SubNat') → SubHom F G
    -- unmap-⟦_⟧ᴾ' (α , _) = unmap-⟦ α ⟧-impl

    isSubHom :
      ∀ (is-sub-Π : {A : Type ℓ} {B : A → Type ℓ} → (∀ a → P (B a)) → P (∀ a → B a))
      → P (SubHom F G)
    isSubHom is-sub-Π = subst P (ua (Σ≃ _)) (P.is-sub-Σ (P.is-sub-→ (G .snd .fst)) λ u → is-sub-Π λ s → P.is-sub-→ (F .snd .snd s))

module Map (F G : Cont) where
  Tf : Type _
  Tf = ∀ X → ⟦ F ⟧ X → ⟦ G ⟧ X

  Tf' : F .Shape → Type _
  Tf' s = ∀ X → (F .Pos s → X) → ⟦ G ⟧ X

  Hom≃IntoExt : Hom F G ≃ ((s : F .Shape) → ⟦ G ⟧ (F .Pos s))
  Hom≃IntoExt =
    Hom F G ≃⟨ _ ≃Σ ⟩
    Σ[ u ∈ (Shape F → Shape G) ] (∀ s → G .Pos (u s) → F .Pos s) ≃⟨ invEquiv Σ-Π-≃ ⟩
    ((s : Shape F) → Σ[ t ∈ Shape G ] (G .Pos t → F .Pos s)) ≃⟨⟩
    ((s : Shape F) → ⟦ G ⟧ (F .Pos s)) ≃∎

  uncurryTfEquiv : ((s : Shape F) → Tf' s) ≃ Tf
  uncurryTfEquiv =
    (∀ s → ∀ X → (F .Pos s → X) → ⟦ G ⟧ X) ≃⟨ flipEquiv ⟩
    (∀ X → ∀ s → (F .Pos s → X) → ⟦ G ⟧ X) ≃⟨ equivΠCod (λ X → invEquiv curryEquiv) ⟩
    (∀ X → (Σ[ s ∈ _ ] (F .Pos s → X)) → ⟦ G ⟧ X) ≃⟨⟩
    (∀ X → ⟦ F ⟧ X → ⟦ G ⟧ X) ≃∎

  mkTf' : (∀ s → ⟦ G ⟧ (F .Pos s)) → (∀ s → Tf' s)
  mkTf' α s X f = map-⟦ mkHomExt α ⟧ X (s , f)

  unTf' : (∀ s → Tf' s) → (∀ s → ⟦ G ⟧ (F .Pos s))
  unTf' α s = α s (F .Pos s) (id $ F .Pos s)

  unTf : Tf → Hom F G
  unTf = invEq uncurryTfEquiv ⋆ unTf' ⋆ invEq Hom≃IntoExt

  _ : unmap-⟦_⟧ ∘ map-⟦_⟧ ≡ id (Hom F G)
  _ = refl

  hasSection-unTf' : hasSection unTf'
  hasSection-unTf' .fst = mkTf'
  hasSection-unTf' .snd _ = refl

  hasSection-unTf : hasSection unTf
  hasSection-unTf .fst = map-⟦_⟧
  hasSection-unTf .snd f = refl

  hasRetract-map-⟦-⟧ : hasRetract map-⟦_⟧
  hasRetract-map-⟦-⟧ .fst = unTf
  hasRetract-map-⟦-⟧ .snd _ = refl

  isSurjection-unmap-⟦-⟧ : isSurjection (unmap-⟦_⟧ {F = F} {G = G})
  isSurjection-unmap-⟦-⟧ = section→isSurjection {g = map-⟦_⟧} λ f → refl

  unmap-⟦-⟧-path : {f g : Hom F G} → map-⟦ f ⟧ ≡ map-⟦ g ⟧ → f ≡ g
  unmap-⟦-⟧-path = cong unmap-⟦_⟧

  unmap-⟦-⟧-path-∙ : {f g h : Hom F G}
    → (p : map-⟦ f ⟧ ≡ map-⟦ g ⟧)
    → (q : map-⟦ g ⟧ ≡ map-⟦ h ⟧)
    → unmap-⟦-⟧-path (p ∙ q) ≡ unmap-⟦-⟧-path p ∙ unmap-⟦-⟧-path q
  unmap-⟦-⟧-path-∙ = cong-∙ unmap-⟦_⟧

  {-
  fibersOfImage-map-⟦-⟧-Equiv : (f : Hom F G) → fiber map-⟦_⟧ map-⟦ f ⟧ ≃ {! !}
  fibersOfImage-map-⟦-⟧-Equiv f =
    fiber map-⟦_⟧ map-⟦ f ⟧ ≃⟨⟩
    Σ[ g ∈ Hom F G ] map-⟦ g ⟧ ≡ map-⟦ f ⟧ ≃⟨ {! !} ⟩
    {! !} ≃∎

  hasPropFibersOfImage-map-⟦-⟧ : (f : Hom F G) → isProp (fiber map-⟦_⟧ map-⟦ f ⟧)
  hasPropFibersOfImage-map-⟦-⟧ f (g₀ , g₀-fib) (g₁ , g₁-fib) = ΣPathP (fib-fst , fib-snd)
    where
      fib-fst : g₀ ≡ g₁
      fib-fst = unmap-⟦-⟧-path (g₀-fib ∙ sym g₁-fib)

      ε : (α : ∀ X → ⟦ F ⟧ X → ⟦ G ⟧ X) → (∀ X → ⟦ F ⟧ X → ⟦ G ⟧ X)
      ε = map-⟦_⟧ ∘ unmap-⟦_⟧

      lemma : cong ε g₀-fib ∙ cong ε (sym g₁-fib) ≡ cong map-⟦_⟧ fib-fst
      lemma =
        cong ε g₀-fib ∙ cong ε (sym g₁-fib) ≡⟨ sym (cong-∙ ε g₀-fib (sym g₁-fib)) ⟩
        cong ε (g₀-fib ∙ sym g₁-fib) ≡⟨⟩
        cong map-⟦_⟧ (cong unmap-⟦_⟧ (g₀-fib ∙ sym g₁-fib)) ≡⟨⟩
        cong map-⟦_⟧ fib-fst ∎

      fib-snd' : PathP (λ i → (cong ε g₀-fib ∙ cong ε (sym g₁-fib)) i ≡ map-⟦ f ⟧) g₀-fib g₁-fib
      fib-snd' = {! cong ε g₀-fib ≡$ _ ≡$ _!}

      fib-snd : PathP (λ i → map-⟦ fib-fst i ⟧ ≡ map-⟦ f ⟧) g₀-fib g₁-fib
      fib-snd = {! !}

      module _ (g : Hom F G) (p : map-⟦ g ⟧ ≡ map-⟦ f ⟧) where
        foo : g .on-shape ≡ f .on-shape
        foo = funExt λ s → cong fst $ p ≡$ (F .Pos s) ≡$ (s , id _)

        bar : PathP (λ i → ∀ s → G .Pos (foo i s) → F .Pos s) (g .on-pos) (f .on-pos)
        bar i s = p i (F .Pos s) (s , id _) .snd

  hasPropFibers-map-⟦-⟧ : (α : ∀ X → ⟦ F ⟧ X → ⟦ G ⟧ X) → isProp (fiber map-⟦_⟧ α)
  hasPropFibers-map-⟦-⟧ α (f , f-fib) (g , g-fib) = ΣPathP (Hom≡ {! f-fib !} {! !} , {! !})
  -}

  isNat→hasSection-map-⟦-⟧ : ∀ α → isNat F G α → map-⟦ unTf α ⟧ ≡ α
  isNat→hasSection-map-⟦-⟧ α is-nat = funExt₂ λ X → uncurry (goal X) where
    module _ (X : Type _) (s : F .Shape) (v : F .Pos s → X) where
      goal : map-⟦ unTf α ⟧ X (s , v) ≡ α X (s , v)
      goal = is-nat _ _ v ≡$ (s , id (F .Pos s))

isTruncCont : (n : HLevel) (F : Cont) → Type ℓ
isTruncCont n F = isOfHLevel n (F .Shape)

module TruncCont (n : HLevel) where
  open import Cubical.Homotopy.Connected
  open import Cubical.HITs.Truncation as Tr using (∥_∥_)
  open import GpdCont.Connectivity

  private
    module _ (n : HLevel) where
      trunc-univ : isUniv {ℓ} (isOfHLevel n)
      trunc-univ .isUniv.is-prop = isPropIsOfHLevel n
      trunc-univ .isUniv.is-sub-Σ = isOfHLevelΣ n
      trunc-univ .isUniv.is-sub-→ is-trunc-B = isOfHLevelΠ n $ const is-trunc-B
      -- trunc-univ .isUniv.is-sub-≡ = isOfHLevelPath n
  
  module TruncCont = Sub (isOfHLevel n) (trunc-univ n) -- (∥_∥ n) Tr.∣_∣ₕ

  open TruncCont renaming
    ( SubHom to TruncHom
    ; SubCont to TruncCont
    ; isSub-⟦_⟧ to isTrunc-⟦_⟧
    ; module Map to TruncMap
    ) public

  module _ (F G : TruncCont) where
    open TruncMap F G renaming
      ( isSubNat to isTruncNat
      ; SubNat to TruncNat
      -- ; SubNat' to TruncNat'
      ; isSubHom to isTruncHom
      ; map-⟦_⟧ᴾ to trunc-map-⟦_⟧
      -- ; map-⟦_⟧ᴾ' to trunc-map-⟦_⟧'
      ; unmap-⟦_⟧ᴾ to trunc-unmap-⟦_⟧
      -- ; unmap-⟦_⟧ᴾ' to trunc-unmap-⟦_⟧'
      )
      public
      
    map-⟦-⟧-retract : hasRetract trunc-map-⟦_⟧
    map-⟦-⟧-retract .fst = trunc-unmap-⟦_⟧
    map-⟦-⟧-retract .snd _ = refl

    isTrunc-trunc-map-⟦-⟧ : (α : TruncNat) → isOfHLevel n (fiber trunc-map-⟦_⟧ α)
    isTrunc-trunc-map-⟦-⟧ = {! isOfHLevelFiber n (isTruncHom (isOfHLevelΠ n)) isOfHLevelSucTruncNat trunc-map-⟦_⟧ !} where
      isOfHLevelTruncNat : isOfHLevel n TruncNat
      isOfHLevelTruncNat = isOfHLevelΣ n
        (isOfHLevelΠ2 n λ X _ → isTrunc-⟦ G ⟧ X)
        λ α → isOfHLevelΠ2 n λ X Y → isOfHLevelΠ n λ g → isOfHLevelPath n (isOfHLevelΠ n λ _ → isTrunc-⟦ G ⟧ Y) _ _

      isOfHLevelSucTruncNat : isOfHLevel (suc n) TruncNat
      isOfHLevelSucTruncNat = isOfHLevelSuc n isOfHLevelTruncNat

    isConn-trunc-map-⟦-⟧→isEquiv-map-⟦-⟧ : isConnectedFun n trunc-map-⟦_⟧ → isEquiv trunc-map-⟦_⟧
    isConn-trunc-map-⟦-⟧→isEquiv-map-⟦-⟧ = {! isTruncFun×isConnectedFun→isEquiv n _ isTrunc-trunc-map-⟦-⟧ !}

  {-
    map-⟦-⟧-section : hasSection trunc-map-⟦_⟧
    map-⟦-⟧-section .fst = trunc-unmap-⟦_⟧
    map-⟦-⟧-section .snd α = {! !}

    map-⟦-⟧'-section : hasSection trunc-map-⟦_⟧'
    map-⟦-⟧'-section .fst = trunc-unmap-⟦_⟧'
    map-⟦-⟧'-section .snd α*@(α , is-nat-α) = ΣPathP (sect , {! !}) where
      sect : trunc-map-⟦_⟧' (trunc-unmap-⟦_⟧' α*) .fst ≡ α
      sect = funExt₂ λ { X (s , v) → goal X s v }
        where module _ (X : TypeOfHLevel ℓ (suc n)) (s : ⟨ Shapeᴾ F ⟩) (v : ⟨ Posᴾ F s ⟩ → ⟨ X ⟩) where
          goal : Path ⟨ ⟦ G ⟧ᴾ X ⟩ (map-⟦ (mkHomExt λ s → α (Posᴾ F s) (s , id ⟨ Posᴾ F s ⟩)) ⟧ ⟨ X ⟩ (s , v)) (α X (s , v))
          goal = Tr.rec (isOfHLevelPath' n (isTrunc-⟦ G ⟧ X) _ _) (λ p → p ≡$ (s , id _)) (is-nat-α (Posᴾ F s) X v)

    isConn-trunc-map-⟦-⟧ : isConnectedFun n trunc-map-⟦_⟧
    isConn-trunc-map-⟦-⟧ = elim.isConnectedPrecompose trunc-map-⟦_⟧ n has-section-precompose where
      has-section-precompose : (P : TruncNat → TypeOfHLevel (ℓ-suc ℓ) n) → hasSection (λ (s : ∀ α → ⟨ P α ⟩) → s ∘ trunc-map-⟦_⟧)
      has-section-precompose P .fst p α = {! p ∘ trunc-unmap-⟦_⟧' !}
      has-section-precompose P .snd = {! !}
  -}

{---
module SetCont where
  open TruncCont 2

  module _ (F G : TruncCont) where
    
    map-⟦-⟧-SetTruncIso : Iso (TruncHom F G) (TruncNat F G)
    map-⟦-⟧-SetTruncIso .Iso.fun = trunc-map-⟦_⟧ F G
    map-⟦-⟧-SetTruncIso .Iso.inv = trunc-unmap-⟦_⟧ F G
    map-⟦-⟧-SetTruncIso .Iso.rightInv α*@(α , is-nat-α) = Σ≡Prop is-prop-is-nat sect where
      is-prop-is-nat : ∀ α → isProp (isTruncNat F G α)
      is-prop-is-nat α = isPropΠ3 λ X Y g → isOfHLevelPath' 1 (isSet→ (isTrunc-⟦ G ⟧ Y)) _ _

      sect : trunc-map-⟦_⟧ F G (trunc-unmap-⟦_⟧ F G α*) .fst ≡ α
      sect = funExt₂ λ { X (s , v) → goal X s v }
        where module _ (X : hSet ℓ) (s : ⟨ Shapeᴾ F ⟩) (v : ⟨ Posᴾ F s ⟩ → ⟨ X ⟩) where
          goal : Path ⟨ ⟦ G ⟧ᴾ X ⟩ (map-⟦ (mkHomExt λ s → α (Posᴾ F s) (s , id ⟨ Posᴾ F s ⟩)) ⟧ ⟨ X ⟩ (s , v)) (α X (s , v))
          goal = is-nat-α (Posᴾ F s) X v ≡$ (s , id _)

    map-⟦-⟧-SetTruncIso .Iso.leftInv f = refl

module GroupoidCont where
  open TruncCont 3

  module _ (F G : TruncCont) where
    private
      F[_] = map-ext {F = F .fst}
      G[_] = map-ext {F = G .fst}

    record isPsNat (α* : TruncNat F G) : Type (ℓ-suc ℓ) where
      open Σ α* renaming (fst to α ; snd to is-nat)

      field
        square : (X Y : hGroupoid ℓ) → (f g : ⟨ X ⟩ → ⟨ Y ⟩) → (θ : f ≡ g)
          → Square
            (is-nat X Y f)
            (is-nat X Y g)
            (cong (λ h → α X ⋆ G[ h ]) θ)
            (cong (λ h → F[ h ] ⋆ α Y) θ)

    has2NatStr : (α : TruncNat F G) → (X Y : hGroupoid ℓ) → (f g : ⟨ X ⟩ → ⟨ Y ⟩) → (θ : f ≡ g) → Type ℓ
    has2NatStr (α , is-nat-α) X Y f g θ = Square (is-nat-α X Y f) (is-nat-α X Y g) left≡ right≡ where
      -- PathP (λ i → left≡ i ≡ right≡ i) (is-nat-α X Y f) (is-nat-α X Y g) where

      left : (⟨ X ⟩ → ⟨ Y ⟩) → ⟨ ⟦ F ⟧ᴾ X ⟩ → ⟨ ⟦ G ⟧ᴾ Y ⟩
      left h = α X ⋆ G[ h ]

      top-left : ⟨ ⟦ F ⟧ᴾ X ⟩ → ⟨ ⟦ G ⟧ᴾ Y ⟩
      top-left = left f

      bot-left : ⟨ ⟦ F ⟧ᴾ X ⟩ → ⟨ ⟦ G ⟧ᴾ Y ⟩
      bot-left = left g

      left≡ : top-left ≡ bot-left
      left≡ = cong left θ

      right : (⟨ X ⟩ → ⟨ Y ⟩) → ⟨ ⟦ F ⟧ᴾ X ⟩ → ⟨ ⟦ G ⟧ᴾ Y ⟩
      right h = F[ h ] ⋆ α Y

      top-right : ⟨ ⟦ F ⟧ᴾ X ⟩ → ⟨ ⟦ G ⟧ᴾ Y ⟩
      top-right = right f

      bot-right : ⟨ ⟦ F ⟧ᴾ X ⟩ → ⟨ ⟦ G ⟧ᴾ Y ⟩
      bot-right = right g

      right≡ : top-right ≡ bot-right
      right≡ = cong right θ


    is2Nat : (α : TruncNat F G) → Type _
    is2Nat α = ∀ (X Y : hGroupoid ℓ) → (f g : ⟨ X ⟩ → ⟨ Y ⟩) → (θ : f ≡ g) → has2NatStr α X Y f g θ


    map-⟦_⟧' = trunc-map-⟦_⟧ F G
    unmap-⟦_⟧' = trunc-unmap-⟦_⟧ F G

    map-⟦-⟧-GroupoidTruncSection : ∀ α → isPsNat α → map-⟦ unmap-⟦ α ⟧' ⟧' ≡ α
    map-⟦-⟧-GroupoidTruncSection α*@(α , is-nat-α) is-psnat-α = ΣPathP (sect , sect-is-nat) where
      module α = isPsNat is-psnat-α

      sect : map-⟦ unmap-⟦ α* ⟧' ⟧' .fst ≡ α
      sect = funExt₂ λ { X (s , v) → goal X s v }
        where module _ (X : hGroupoid ℓ) (s : ⟨ Shapeᴾ F ⟩) (v : ⟨ Posᴾ F s ⟩ → ⟨ X ⟩) where
          goal : map-⟦ (mkHomExt λ s → α (Posᴾ F s) (s , id ⟨ Posᴾ F s ⟩)) ⟧ ⟨ X ⟩ (s , v) ≡ α X (s , v)
          goal = is-nat-α (Posᴾ F s) X v ≡$ (s , id _)

      module _ (X Y : hGroupoid ℓ) (g : ⟨ X ⟩ → ⟨ Y ⟩) (s : ⟨ Shapeᴾ F ⟩) (v : ⟨ Posᴾ F s ⟩ → ⟨ X ⟩) where
        -- sect-is-nat-ext-fst : Square {A = ⟨ Shapeᴾ G ⟩}
        --   (refl′ $ α (Posᴾ F s) (s , id (F .fst .Pos s)) .fst)
        --   (λ j → is-nat-α X Y g j (s , v) .fst)
        --   (λ i → is-nat-α (Posᴾ F s) X v i (s , id _) .fst)
        --   (λ i → is-nat-α (Posᴾ F s) Y (v ⋆ g) i (s , id _) .fst)
        -- sect-is-nat-ext-fst i j = {! !}

        -- lemma : (xx : ? → ⟨ ⟦ G ⟧ᴾ ? ⟩) → G[ g ] (xx (s , id _)) ≡ xx (s , v)
        -- lemma xx = {! !}
        
        testme : (f g : ⟨ X ⟩ → ⟨ Y ⟩) → (θ : f ≡ g) → (cong (λ h → α X ⋆ G[ h ]) θ) ∙ (is-nat-α X Y g) ≡ (is-nat-α X Y f) ∙ (cong (λ h → F[ h ] ⋆ α Y) θ)
        testme f g θ = Square→compPath (α.square X Y f g θ)

        sect-is-nat-ext : Square {A = ⟨ ⟦ G ⟧ᴾ Y ⟩}
          (refl′ $ G[ g ] $ map-⟦ unmap-⟦ α* ⟧' ⟧ ⟨ X ⟩ (s , v))
          -- (λ j → α (Posᴾ F s) (s , id (F .fst .Pos s)) .fst , α _ (s , id _) .snd ⋆ v ⋆ g)
          (is-nat-α X Y g ≡$ (s , v))
          -- (λ i → map-ext g (is-nat-α (Posᴾ F s) X v i (s , id _)))
          (cong G[ g ] (is-nat-α (Posᴾ F s) X v ≡$ (s , id _)))
          -- (λ i → is-nat-α (Posᴾ F s) Y (v ⋆ g) i (s , id _))
          (is-nat-α (Posᴾ F s) Y (v ⋆ g) ≡$ (s , id _))
        sect-is-nat-ext = compPath→Square $
          (cong G[ g ] (is-nat-α (Posᴾ F s) X v ≡$ (s , id _))) ∙ (is-nat-α X Y g ≡$ (s , v)) ≡⟨⟩
          (cong G[ g ] $ cong (_$ (s , id _)) (is-nat-α (Posᴾ F s) X v)) ∙ (cong (_$ (s , v)) $ is-nat-α X Y g) ≡⟨⟩
          (cong (G[ g ] ∘ (_$ (s , id _))) $ is-nat-α (Posᴾ F s) X v) ∙ (cong (_$ (s , v)) $ is-nat-α X Y g) ≡⟨ {! !} ⟩
          (λ i → G[ g ] $ is-nat-α (Posᴾ F s) X v i (s , id _)) ∙ (cong (_$ (s , v)) $ is-nat-α X Y g) ≡⟨ {! !} ⟩
          (is-nat-α (Posᴾ F s) Y (v ⋆ g) ≡$ (s , id _)) ≡⟨ {! !} ⟩
          (refl′ _) ∙ (is-nat-α (Posᴾ F s) Y (v ⋆ g) ≡$ (s , id _)) ∎

      module _ (X Y : hGroupoid ℓ) (g : ⟨ X ⟩ → ⟨ Y ⟩) where
        private
          α' = map-⟦ unmap-⟦ α* ⟧' ⟧'

          g' = α' .snd X Y g

        sect-is-nat' : Square
          (α' .snd X Y g)
          (is-nat-α X Y g)
          (cong (λ α → α X ⋆ G[ g ]) sect)
          (cong (λ α → F[ g ] ⋆ α Y) sect)
        sect-is-nat' = {! α.square X Y _ g _ !}

      sect-is-nat : PathP (λ i → isTruncNat F G (sect i)) (map-⟦ unmap-⟦ α* ⟧' ⟧' .snd) is-nat-α
      sect-is-nat = funExt₃ λ X Y g → funExtSquare $ uncurry $ sect-is-nat-ext X Y g

    map-⟦-⟧-GroupoidTruncPathSplitEquiv : PathSplitEquiv (TruncNat F G) (TruncHom F G)
    map-⟦-⟧-GroupoidTruncPathSplitEquiv .fst = unmap-⟦_⟧'
    map-⟦-⟧-GroupoidTruncPathSplitEquiv .snd = {! !}

    map-⟦-⟧-GroupoidTruncIso : Iso (TruncHom F G) (TruncNat F G)
    map-⟦-⟧-GroupoidTruncIso .Iso.fun = map-⟦_⟧'
    map-⟦-⟧-GroupoidTruncIso .Iso.inv = unmap-⟦_⟧'
    map-⟦-⟧-GroupoidTruncIso .Iso.rightInv α*@(α , is-nat-α) = ΣPathP (sect , sect-is-nat) where
      sect : map-⟦ unmap-⟦ α* ⟧' ⟧' .fst ≡ α
      sect = funExt₂ λ { X (s , v) → goal X s v }
        where module _ (X : hGroupoid ℓ) (s : ⟨ Shapeᴾ F ⟩) (v : ⟨ Posᴾ F s ⟩ → ⟨ X ⟩) where
          goal : map-⟦ (mkHomExt λ s → α (Posᴾ F s) (s , id ⟨ Posᴾ F s ⟩)) ⟧ ⟨ X ⟩ (s , v) ≡ α X (s , v)
          goal = is-nat-α (Posᴾ F s) X v ≡$ (s , id _)

      module _ (X Y : hGroupoid ℓ) (g : ⟨ X ⟩ → ⟨ Y ⟩) (s : ⟨ Shapeᴾ F ⟩) (v : ⟨ Posᴾ F s ⟩ → ⟨ X ⟩) where
        sect-is-nat-ext-fst : Square {A = ⟨ Shapeᴾ G ⟩}
          (refl′ $ α (Posᴾ F s) (s , id (F .fst .Pos s)) .fst)
          (λ j → is-nat-α X Y g j (s , v) .fst)
          (λ i → is-nat-α (Posᴾ F s) X v i (s , id _) .fst)
          (λ i → is-nat-α (Posᴾ F s) Y (v ⋆ g) i (s , id _) .fst)
        sect-is-nat-ext-fst i j = {! !}

        sect-is-nat-ext : SquareP (λ i j → ⟨ ⟦ G ⟧ᴾ Y ⟩)
          -- (λ j → map-ext g $ map-⟦ mkHomExt (λ s → α (Posᴾ F s) (s , id _)) ⟧ ⟨ X ⟩ (s , v))
          (λ j → α (Posᴾ F s) (s , id (F .fst .Pos s)) .fst , α _ (s , id _) .snd ⋆ v ⋆ g)
          (λ j → is-nat-α X Y g j (s , v))
          -- (λ i → map-ext g (is-nat-α (Posᴾ F s) X v i (s , id _)))
          (λ i → is-nat-α (Posᴾ F s) X v i (s , id _) .fst , is-nat-α (Posᴾ F s) X v i (s , id _) .snd ⋆ g)
          (λ i → is-nat-α (Posᴾ F s) Y (v ⋆ g) i (s , id _))
        sect-is-nat-ext i j .fst = {! !}
        sect-is-nat-ext i j .snd = {! !}

      sect-is-nat : PathP (λ i → isTruncNat F G (sect i)) (map-⟦ unmap-⟦ α* ⟧' ⟧' .snd) is-nat-α
      sect-is-nat = funExt₃ λ X Y g → funExtSquare $ uncurry $ sect-is-nat-ext X Y g
    map-⟦-⟧-GroupoidTruncIso .Iso.leftInv f = refl
    ---}

private
  module _ {ℓA ℓB} (A : Type ℓA) (B : Type ℓB) where
    π : A → (B → A)
    π a _ = a

    _ : π ≡ curry fst
    _ = refl

    isNull : Type _
    isNull = isEquiv π

  PA : (ℓ : Level) → Type _
  PA ℓ = (A : Type ℓ) → isNull A (Type ℓ)

  _ : ∀ {ℓ} → PA ℓ ≡ (∀ A → isEquiv (π A (Type ℓ)))
  _ = refl

  PA' : (ℓ : Level) → Type _
  PA' ℓ = (A : Type ℓ) → isEquiv (the (A → (X : Type ℓ) → (A → X) → X) (λ a _ f → f a))

  PA'→PA : ∀ {ℓ} → PA' ℓ → PA ℓ
  PA'→PA pa' A = {! !} where
    foo : A → (f : Σ[ X ∈ Type ℓ ] (A → X)) → f .fst
    foo a (_ , f) = f a
    
    is-equiv-foo : isEquiv foo
    is-equiv-foo = {! !}

  module _ {ℓ} (F : Type ℓ → Type ℓ) where
    coYo : (A : Type ℓ) → ((X : Type ℓ) → (A → X) → F X) → F A
    coYo A α = α A (id A)

    hasCoYo : Type _
    hasCoYo = (A : Type ℓ) → isEmbedding (coYo A)

    PA→hasCoYo : (∀ {ℓ} → PA ℓ) → hasCoYo
    PA→hasCoYo pa A = goal where
      _ : isEquiv (the (F A → (X : Type ℓ) → F A) $ π (F A) (Type ℓ))
      _ = pa (F A)

      coYo[_,_] : (α β : ∀ X → (A → X) → F X) → α ≡ β → coYo A α ≡ coYo A β
      coYo[ α , β ] = cong (coYo A)

      test : (α β : ∀ X → (A → X) → F X) → coYo[ α , β ] ≡ (λ p i → p i A (id A))
      test α β = refl

      module _ (α β : ∀ X → (A → X) → F X) where
        crunch : (α ≡ β) ≃ (coYo A α ≡ coYo A β)
        crunch =
          (α ≡ β) ≃⟨ {! !} ⟩
          (∀ X f → α X f ≡ β X f) ≃⟨ {! pa (Σ[ X ∈ Type ℓ ] (A → X)) !} ⟩
          (coYo A α ≡ coYo A β) ≃∎
      goal : (α β : ∀ X → (A → X) → F X) → isEquiv coYo[ α , β ]
      goal α β = {! pa (α ≡ β) !}

module _ (F G : Cont) where

  foo : (∀ X → ⟦ F ⟧ X ≡ ⟦ G ⟧ X) → F ≡ G
  foo p = Cont≡ (λ i → {! p (G .Shape)!}) {! !}

  is-embedding-⟦-⟧ : ∀ α → isProp (fiber ⟦_⟧ α)
  is-embedding-⟦-⟧ α (F , p) (Q , q) = ΣPathP ({! !} , {! !})

  embedd : (F ≡ G) ≃ (⟦ F ⟧ ≡ ⟦ G ⟧)
  embedd =
    (F ≡ G) ≃⟨ {! !} ⟩
    (∀ X → {! !}) ≃⟨ equivΠCod (λ X → {! ⟦ F ⟧ X!}) ⟩
    (∀ X → ⟦ F ⟧ X ≡ ⟦ G ⟧ X) ≃⟨ funExtEquiv ⟩
    (⟦ F ⟧ ≡ ⟦ G ⟧) ≃∎
