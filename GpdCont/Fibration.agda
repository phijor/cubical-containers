module GpdCont.Fibration where

open import GpdCont.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
  using (hasSection)
  public
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism as Isomorphism
  using (Iso ; invIso ; section ; _Iso⟨_⟩_)
  renaming (_∎Iso to _Iso∎)
open import Cubical.Data.Sigma.Properties as Sigma

open Iso

private
  variable
    ℓ : Level
    X Y : Type ℓ
    A : Type ℓ
    B : A → Type ℓ

Section : (B : A → Type ℓ) → Type _
Section {A} B = (a : A) → B a

isOfHLevelSection : (n : HLevel) → (∀ a → isOfHLevel n (B a)) → isOfHLevel n (Section B)
isOfHLevelSection n = isOfHLevelΠ n

hasSection-fiberSection-Iso : (f : X → Y) → Iso (hasSection f) (Section $ fiber f)
hasSection-fiberSection-Iso f = invIso Sigma.Σ-Π-Iso

module Total (X : Type ℓ) (Y : X → Type ℓ) where
  Total : Type _
  Total = Σ[ x ∈ X ] (Y x)

  isOfHLevelTotal : ∀ n → isOfHLevel n X → (∀ x → isOfHLevel n (Y x)) → isOfHLevel n Total
  isOfHLevelTotal = isOfHLevelΣ

  proj : Total → X
  proj = fst

  fiber-proj→Family : ∀ x → fiber proj x → Y x
  fiber-proj→Family x ((x′ , y′) , p) = subst Y p y′

  Family→fiber-proj : ∀ x → Y x → fiber proj x
  Family→fiber-proj x y .fst = x , y
  Family→fiber-proj x y .snd = refl

  -- This is essentially contractibility of singletons around x:
  fiberProj-Family-Iso : ∀ x → Iso (fiber proj x) (Y x)
  fiberProj-Family-Iso x .Iso.fun = fiber-proj→Family x
  fiberProj-Family-Iso x .Iso.inv = Family→fiber-proj x
  fiberProj-Family-Iso x .Iso.rightInv y = substRefl {B = Y} y
  fiberProj-Family-Iso x .Iso.leftInv t@((x′ , y′) , p) = sym left-inv where
    left-inv : t ≡ Family→fiber-proj x (fiber-proj→Family x t)
    left-inv i .fst .fst = p i
    left-inv i .fst .snd = subst-filler Y p y′ i
    left-inv i .snd j = p (i ∨ j)

  hasSectionProj-SectionFam-Iso : Iso (hasSection proj) (Section Y)
  hasSectionProj-SectionFam-Iso =
    hasSection proj       Iso⟨ hasSection-fiberSection-Iso proj ⟩
    Section (fiber proj)  Iso⟨ Isomorphism.codomainIsoDep fiberProj-Family-Iso ⟩
    Section Y             Iso∎
