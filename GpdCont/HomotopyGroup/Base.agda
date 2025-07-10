module GpdCont.HomotopyGroup.Base where

open import GpdCont.Prelude
open import GpdCont.Connectivity

open import GpdCont.StrictGroupoid.Base renaming (elimProp to elimProp')

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed.Base as Pointed using (Pointed)
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  variable
    ℓ : Level

isHGroup : StrictGroupoid ℓ → Type ℓ
isHGroup G = isPathConnected ⟨ G ⟩

isPropIsHGroup : (G : StrictGroupoid ℓ) → isProp (isHGroup G)
isPropIsHGroup G = isPropIsPathConnected ⟨ G ⟩

hGroup : (ℓ : Level) → Type (ℓ-suc ℓ)
hGroup ℓ = Σ[ G ∈ StrictGroupoid ℓ ] isHGroup G

⟨_⟩ᵗ : hGroup ℓ → Type ℓ
⟨ (G , _) , _ ⟩ᵗ = G
-- {-# INJECTIVE_FOR_INFERENCE ⟨_⟩ᵗ #-}

module hGroup (G : hGroup ℓ) where
  open StrictGroupoidStr (str (G .fst)) public

  Tr : Type _
  Tr = ∥ ⟨ G .fst ⟩ ∥₂

  is-connected : isPathConnected ⟨ G .fst ⟩
  is-connected = G .snd

  center : Tr
  center = is-connected .fst

  centerElimEquiv : ∀ {ℓB} {B : Tr → Type ℓB}
    → B center ≃ (∀ x → B x)
  centerElimEquiv {B} = invEquiv (Π-contractDom is-connected)

  centerElim : ∀ {ℓB} {B : ∥ ⟨ G .fst ⟩ ∥₂ → Type ℓB}
    → B center
    → ∀ x → B x
  centerElim = equivFun centerElimEquiv

  pt₀ : ⟨ G .fst ⟩
  pt₀ = pt center

  asPointed : Pointed ℓ
  asPointed .fst = ⟨ G .fst ⟩
  asPointed .snd = pt₀

  asGroupoid : hGroupoid ℓ
  asGroupoid .fst = ⟨ G . fst ⟩
  asGroupoid .snd = is-groupoid

  mere-path : ∀ g → ∥ pt₀ ≡ g ∥₁
  mere-path g = isPathConnected→merePath is-connected pt₀ g

  elimProp : ∀ {ℓP} {P : ⟨ G ⟩ᵗ → Type ℓP}
    → (∀ g → isProp (P g))
    → (P pt₀)
    → ∀ g → P g
  elimProp {P} is-prop-P p₀ = elimProp' (G .fst) is-prop-P p* where
    -- G has a unique connected component,
    -- so the domain of this map is contractible:
    p* : (x : ∥ ⟨ G .fst ⟩ ∥₂) → P (pt x)
    p* = Π-contractDomIso is-connected .Iso.inv p₀

  elimPropᵝ : ∀ {ℓP} {P : ⟨ G ⟩ᵗ → Type ℓP}
    → (is-prop-P : ∀ g → isProp (P g))
    → (p₀ : P pt₀)
    → elimProp is-prop-P p₀ pt₀ ≡ p₀
  elimPropᵝ is-prop-P p₀ = is-prop-P _ _ p₀

  module _ {ℓX} {X : Type ℓX} (is-set-X : isSet X) where
    recSetEquiv : X ≃ (⟨ G ⟩ᵗ → X)
    recSetEquiv = isPathConnected→constEquiv is-connected is-set-X

    recSet : (x₀ : X) → ⟨ G ⟩ᵗ → X
    recSet = equivFun recSetEquiv

  {-
  elimConnected : {X : ⟨ G ⟩ᵗ → Type ℓX} (is-conn-X : ∀ g → isPathConnected (X g))
    → (x₀ : X pt₀)
    → ∀ g → X g
  elimConnected is-conn-X x₀ = isConnectedPoint.elim 1 (isPathConnected→is2Connected is-connected) {! !} {! !}

  elimSet' : {X : ⟨ G ⟩ᵗ → Type ℓX} (is-set-X : ∀ g → isSet (X g))
    → (x₀ : X pt₀)
    → {! !}
    → ∀ g → X g
  elimSet' {X} is-set-X x₀ p = {! recSet  !}

  elimSet : {X : ⟨ G ⟩ᵗ → Type ℓX} (is-set-X : ∀ g → isSet (X g))
    → (x₀ : X pt₀)
    → {! !}
    → ∀ g → X g
  elimSet {X} is-set-X x₀ p g = PT.elim→Set {! !} f {! !} (mere-path g) where
    f : pt₀ ≡ g → X g
    f p = subst X p x₀

    f-filler : (p : pt₀ ≡ g) → PathP (λ i → X (p i)) x₀ (f p)
    f-filler p = subst-filler X p x₀

    link : (p q : pt₀ ≡ g) → f p ≡ f q
    link p q = {!doubleCompPathP (λ i j → X (p i)) (f-filler p) !}
  -}

hGroup≡ : ∀ {G H : hGroup ℓ} → G .fst ≡ H .fst → G ≡ H
hGroup≡ = Σ≡Prop isPropIsHGroup

pointedConnectedGroupoid→hGroup : ∀ (G : Type ℓ)
  → (g₀ : G)
  → isPathConnected G
  → isGroupoid G
  → hGroup ℓ
pointedConnectedGroupoid→hGroup G g₀ is-conn-G is-groupoid-G = G* where
  G* : hGroup _
  G* .fst .fst = G
  G* .fst .snd .StrictGroupoidStr.is-groupoid = is-groupoid-G
  G* .fst .snd .StrictGroupoidStr.pt = const g₀
  G* .fst .snd .StrictGroupoidStr.pt-section = isContr→isProp is-conn-G ∣ g₀ ∣₂
  G* .snd = is-conn-G

isTrivial : (G : hGroup ℓ) → Type ℓ
isTrivial G = isContr ⟨ G ⟩ᵗ

isSet→isTrivial : (G : hGroup ℓ) → isSet ⟨ G ⟩ᵗ → isTrivial G
isSet→isTrivial G is-set-G = isOfHLevel×isConnected→isContr 2 ⟨ G ⟩ᵗ is-set-G $ isPathConnected→is2Connected $ hGroup.is-connected G
