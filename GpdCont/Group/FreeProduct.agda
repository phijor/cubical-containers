module GpdCont.Group.FreeProduct where

open import GpdCont.Prelude

open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties renaming (compGroupHom to _∙ᴳ_)

module _ {ℓG ℓH} (G : Group ℓG) (H : Group ℓH) where
  private
    module G = GroupStr (str G)
    module H = GroupStr (str H)

  data FreeProduct : Type (ℓ-max ℓG ℓH) where
    inl : ⟨ G ⟩ → FreeProduct
    inr : ⟨ H ⟩ → FreeProduct

    ε : FreeProduct
    ε-inl : inl G.1g ≡ ε
    ε-inr : inr H.1g ≡ ε

    _·_ : FreeProduct → FreeProduct → FreeProduct
    ·-inl : ∀ g g' → inl (g G.· g') ≡ inl g · inl g'
    ·-inr : ∀ h h' → inr (h H.· h') ≡ inr h · inr h'

    inv : FreeProduct → FreeProduct
    inv-inl : ∀ g → inl (G.inv g) ≡ inv (inl g)
    inv-inr : ∀ h → inr (H.inv h) ≡ inv (inr h)

    assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
    idr : ∀ x → x · ε ≡ x
    idl : ∀ x → ε · x ≡ x

    invr : ∀ x → x · (inv x) ≡ ε
    invl : ∀ x → (inv x) · x ≡ ε

    isSetFreeProduct : isSet FreeProduct

  isGroupFreeProduct : IsGroup ε _·_ inv
  isGroupFreeProduct = makeIsGroup isSetFreeProduct
    assoc
    idr
    idl
    invr
    invl

  FreeProductGroup : Group _
  FreeProductGroup .fst = FreeProduct
  FreeProductGroup .snd .GroupStr.1g = _
  FreeProductGroup .snd .GroupStr._·_ = _
  FreeProductGroup .snd .GroupStr.inv = _
  FreeProductGroup .snd .GroupStr.isGroup = isGroupFreeProduct

  inlHom : GroupHom G FreeProductGroup
  inlHom .fst = inl
  inlHom .snd .IsGroupHom.pres· = ·-inl
  inlHom .snd .IsGroupHom.pres1 = ε-inl
  inlHom .snd .IsGroupHom.presinv = inv-inl

  inrHom : GroupHom H FreeProductGroup
  inrHom .fst = inr
  inrHom .snd .IsGroupHom.pres· = ·-inr
  inrHom .snd .IsGroupHom.pres1 = ε-inr
  inrHom .snd .IsGroupHom.presinv = inv-inr

  module _ {ℓK} (K : Group ℓK) (φ : GroupHom G K) (ψ : GroupHom H K) where
    private
      module K = GroupStr (str K)
      module φ = IsGroupHom (φ .snd)
      module ψ = IsGroupHom (ψ .snd)

    coparing : FreeProduct → ⟨ K ⟩
    coparing (inl g) = φ .fst g
    coparing (inr h) = ψ .fst h
    coparing ε = K.1g
    coparing (ε-inl i) = φ.pres1 i
    coparing (ε-inr i) = ψ.pres1 i
    coparing (x · y) = coparing x K.· coparing y
    coparing (·-inl g g' i) = φ.pres· g g' i
    coparing (·-inr h h' i) = ψ.pres· h h' i
    coparing (inv x) = K.inv (coparing x)
    coparing (inv-inl g i) = φ.presinv g i
    coparing (inv-inr h i) = ψ.presinv h i
    coparing (assoc x y z i) = K.·Assoc (coparing x) (coparing y) (coparing z) i
    coparing (idr x i) = K.·IdR (coparing x) i
    coparing (idl x i) = K.·IdL (coparing x) i
    coparing (invr x i) = K.·InvR (coparing x) i
    coparing (invl x i) = K.·InvL (coparing x) i
    coparing (isSetFreeProduct x y p q i j) = K.is-set (coparing x) (coparing y) (cong coparing p) (cong coparing q) i j

    coparingHom : GroupHom FreeProductGroup K
    coparingHom .fst = coparing
    coparingHom .snd .IsGroupHom.pres· _ _ = refl
    coparingHom .snd .IsGroupHom.pres1 = refl
    coparingHom .snd .IsGroupHom.presinv _ = refl

    isCoproductFreeProductGroup : ∃![ ω ∈ GroupHom FreeProductGroup K ] (inlHom ∙ᴳ ω ≡ φ) × (inrHom ∙ᴳ ω ≡ ψ)
    isCoproductFreeProductGroup .fst .fst = coparingHom
    isCoproductFreeProductGroup .fst .snd .fst = GroupHom≡ refl
    isCoproductFreeProductGroup .fst .snd .snd = GroupHom≡ refl
    isCoproductFreeProductGroup .snd (ω , ω-inl , ω-inr) = Σ≡Prop (λ ω → isProp× (isSetGroupHom _ _) (isSetGroupHom _ _))
      $ GroupHom≡ $ sym $ funExt λ where
        (inl g) → cong fst ω-inl ≡$ g
        (inr h) → cong fst ω-inr ≡$ h
        ε → ω.pres1
        (ε-inl i) → K.is-set _ _ {! ω-inl i .snd .IsGroupHom.pres1!} _ i
        (ε-inr i) → {! !}
        (x · y) → {! !}
        (·-inl g g' i) → {! !}
        (·-inr h h' i) → {! !}
        (inv x) → {! !}
        (inv-inl g i) → {! !}
        (inv-inr h i) → {! !}
        (assoc x y z i) → {! !}
        (idr x i) → {! !}
        (idl x i) → {! !}
        (invr x i) → {! !}
        (invl x i) → {! !}
        (isSetFreeProduct x x₁ x₂ y i i₁) → {! !}
      where
        module ω = IsGroupHom (ω .snd)
