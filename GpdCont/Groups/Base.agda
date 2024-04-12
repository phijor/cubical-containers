module GpdCont.Groups.Base where

open import GpdCont.Prelude
open import GpdCont.RecordEquiv

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.PropositionalTruncation.Monad using (_>>=_ ; return)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto using (autoDUARel)
open import Cubical.Displayed.Universe using () renaming (𝒮-Univ to UnivalenceUARel)
open import Cubical.Displayed.Record

record GroupStr {ℓ} (G : Type ℓ) : Type ℓ where
  field
    is-connected : isContr ∥ G ∥₂
    is-groupoid : isGroupoid G
    pt : G

  existsPath : (g h : G) → ∥ g ≡ h ∥₁
  existsPath g h = ST.PathIdTrunc₀Iso {a = g} {b = h} .Iso.fun (isContr→isProp is-connected ST.∣ g ∣₂ ST.∣ h ∣₂)

  -- weak-pt : ∥ G ∥₁
  -- weak-pt = ST.rec (isProp→isSet PT.isPropPropTrunc) PT.∣_∣₁ (is-connected .fst)

  -- mere-fiber : ∀ h → ∥ Σ[ ⋆ ∈ G ] ⋆ ≡ h ∥₁
  -- mere-fiber h = do
  --   ⋆ ← weak-pt
  --   p ← existsPath ⋆ h
  --   return (⋆ , p)

  -- loopy : ∥ Σ[ ⋆ ∈ G ] ⋆ ≡ ⋆ ∥₂
  -- loopy = {! !}

  -- pt' : G
  -- pt' = ST.rec→Gpd.fun is-groupoid fst coh loopy where
  --   coh : ∀ (x y : Σ[ ⋆ ∈ G ] ⋆ ≡ ⋆) → (p q : x ≡ y) → cong fst p ≡ cong fst q
  --   coh (⋆₁ , ω₁) (⋆₂ , ω₂) p q i j = {! !}

Group : (ℓ : Level) → Type _
Group ℓ = TypeWithStr ℓ GroupStr

unquoteDecl GroupStrIsoΣ = declareRecordIsoΣ GroupStrIsoΣ (quote GroupStr)

instance
  GroupStrToΣ : ∀ {ℓ} {G : Type ℓ} → RecordToΣ (GroupStr G)
  GroupStrToΣ = toΣ GroupStrIsoΣ

open GroupStr
GroupStrPath : ∀ {ℓ} {G : Type ℓ} {s₀ s₁ : GroupStr G}
  → (s₀ .pt ≡ s₁ .pt) → (s₀ ≡ s₁)
GroupStrPath {s₀} {s₁} p i = go where
  go : GroupStr _
  go .is-connected = isProp→PathP (λ i → isPropIsContr) (s₀ .is-connected) (s₁ .is-connected) i
  go .is-groupoid = isProp→PathP (λ i → isPropIsGroupoid) (s₀ .is-groupoid) (s₁ .is-groupoid) i
  go .pt = p i
