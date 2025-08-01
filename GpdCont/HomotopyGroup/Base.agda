module GpdCont.HomotopyGroup.Base where

open import GpdCont.Prelude
open import GpdCont.Connectivity

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed.Base as Pointed using (Pointed)
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  variable
    ℓ : Level

record hGroupStr {ℓ} (G : Type ℓ) : Type (ℓ-suc ℓ) where
  no-eta-equality
  field
    pt₀ : G
    is-connected : isPathConnected G
    is-groupoid : isGroupoid G
    

record hGroup (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    ⟨_⟩ᵗ : Type ℓ
    hgroup-str : hGroupStr ⟨_⟩ᵗ

  open hGroupStr hgroup-str public

  asPointed : Pointed ℓ
  asPointed .fst = ⟨_⟩ᵗ
  asPointed .snd = pt₀

  asGroupoid : hGroupoid ℓ
  asGroupoid .fst = ⟨_⟩ᵗ
  asGroupoid .snd = is-groupoid

  mere-path : ∀ g → ∥ pt₀ ≡ g ∥₁
  mere-path g = isPathConnected→merePath is-connected pt₀ g

  elimProp : ∀ {ℓP} {P : ⟨_⟩ᵗ → Type ℓP}
    → (∀ g → isProp (P g))
    → (P pt₀)
    → ∀ g → P g
  elimProp {P} is-prop-P p₀ g = PT.rec {A = pt₀ ≡ g} (is-prop-P g) p* (mere-path g) where
    p* : ∀ {g} → pt₀ ≡ g → P g
    p* pt₀≡g = subst P pt₀≡g p₀

  elimPropᵝ : ∀ {ℓP} {P : ⟨_⟩ᵗ → Type ℓP}
    → (is-prop-P : ∀ g → isProp (P g))
    → (p₀ : P pt₀)
    → elimProp is-prop-P p₀ pt₀ ≡ p₀
  elimPropᵝ is-prop-P p₀ = is-prop-P _ _ p₀

  module _ {ℓX} {X : Type ℓX} (is-set-X : isSet X) where
    recSetEquiv : X ≃ (⟨_⟩ᵗ → X)
    recSetEquiv = isPathConnected→constEquiv is-connected is-set-X

    recSet : (x₀ : X) → ⟨_⟩ᵗ → X
    recSet = equivFun recSetEquiv

open hGroup using (⟨_⟩ᵗ) public

pointedConnectedGroupoid→hGroup : ∀ (G : Type ℓ)
  → (g₀ : G)
  → isPathConnected G
  → isGroupoid G
  → hGroup ℓ
pointedConnectedGroupoid→hGroup G g₀ is-conn-G is-groupoid-G = G* where
  G* : hGroup _
  G* .hGroup.⟨_⟩ᵗ = G
  G* .hGroup.hgroup-str .hGroupStr.pt₀ = g₀
  G* .hGroup.hgroup-str .hGroupStr.is-connected = is-conn-G
  G* .hGroup.hgroup-str .hGroupStr.is-groupoid = is-groupoid-G

isTrivial : (G : hGroup ℓ) → Type ℓ
isTrivial G = isContr ⟨ G ⟩ᵗ

isSet→isTrivial : (G : hGroup ℓ) → isSet ⟨ G ⟩ᵗ → isTrivial G
isSet→isTrivial G is-set-G = isOfHLevel×isConnected→isContr 2 ⟨ G ⟩ᵗ is-set-G $ isPathConnected→is2Connected $ hGroup.is-connected G
