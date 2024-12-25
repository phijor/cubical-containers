open import GpdCont.Prelude
open import GpdCont.Group.DeloopingCategory

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path as Path
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Foundations.GroupoidLaws using (compPathRefl)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.StructureOver

module GpdCont.Group.MapConjugator {ℓ} {G H : Group ℓ} where
  private
    open module H = GroupStr (str H) using (_·_)

    variable
      φ ψ : GroupHom G H

  isConjugator : (φ ψ : GroupHom G H) → ⟨ H ⟩ → Type ℓ
  isConjugator (φ , _) (ψ , _) h = ∀ (g : ⟨ G ⟩) → φ g · h ≡ h · ψ g

  opaque
    isPropIsConjugator : {φ ψ : GroupHom G H} → ∀ h → isProp (isConjugator φ ψ h)
    isPropIsConjugator h = isPropΠ λ g → H.is-set _ _

  opaque
    isConjugator1 : (φ : GroupHom G H) → isConjugator φ φ H.1g
    isConjugator1 φ = λ g → H.·IdR _ ∙ sym (H.·IdL _)

  opaque
    isConjugator-· : (φ ψ ρ : GroupHom G H) → ∀ h₁ h₂
      → isConjugator φ ψ h₁
      → isConjugator ψ ρ h₂
      → isConjugator φ ρ (h₁ · h₂)
    isConjugator-· (φ , _) (ψ , _) (ρ , _) h₁ h₂ conj-h₁ conj-h₂ g =
      φ g · (h₁ · h₂) ≡⟨ H.·Assoc _ _ _ ⟩
      (φ g · h₁) · h₂ ≡⟨ cong (_· h₂) (conj-h₁ g) ⟩
      (h₁ · ψ g) · h₂ ≡⟨ sym $ H.·Assoc _ _ _ ⟩
      h₁ · (ψ g · h₂) ≡⟨ cong (h₁ ·_) (conj-h₂ g) ⟩
      h₁ · (h₂ · ρ g) ≡⟨ H.·Assoc _ _ _ ⟩
      (h₁ · h₂) · ρ g ∎

  Conjugator : (φ ψ : GroupHom G H) → Type ℓ
  Conjugator φ ψ = Σ ⟨ H ⟩ (isConjugator φ ψ)

  isSetConjugator : (φ ψ : GroupHom G H) → isSet (Conjugator φ ψ)
  isSetConjugator φ ψ = isSetΣSndProp H.is-set $ isPropIsConjugator {φ} {ψ}

  ConjugatorPathP : {φ φ′ ψ ψ′ : GroupHom G H}
    → {p : φ ≡ φ′} {q : ψ ≡ ψ′}
    → {h₁ : Conjugator φ ψ}
    → {h₂ : Conjugator φ′ ψ′}
    → h₁ .fst ≡ h₂ .fst
    → PathP (λ i → Conjugator (p i) (q i)) h₁ h₂
  ConjugatorPathP h-path i .fst = h-path i
  ConjugatorPathP {p} {q} {h₁} {h₂} h-path i .snd =
    isProp→PathP {B = λ i → isConjugator (p i) (q i) (h-path i)}
      (λ i → isPropIsConjugator {φ = p i} {ψ = q i} (h-path i))
      (h₁ .snd)
      (h₂ .snd)
      i

  Conjugator≡ : {φ ψ : GroupHom G H} → {h₁ h₂ : Conjugator φ ψ} → h₁ .fst ≡ h₂ .fst → h₁ ≡ h₂
  Conjugator≡ {φ} {ψ} = Σ≡Prop $ isPropIsConjugator {φ} {ψ}

  idConjugator : (φ : GroupHom G H) → Conjugator φ φ
  idConjugator φ .fst = H.1g
  idConjugator φ .snd = isConjugator1 φ

  compConjugator : {φ ψ ρ : GroupHom G H} → Conjugator φ ψ → Conjugator ψ ρ → Conjugator φ ρ
  compConjugator (h₁ , h₁-conj) (h₂ , h₂-conj) .fst = h₁ · h₂
  compConjugator {φ} {ψ} {ρ} (h₁ , h₁-conj) (h₂ , h₂-conj) .snd = isConjugator-· φ ψ ρ h₁ h₂ h₁-conj h₂-conj

  ConjugatorStr : StructureOver (DeloopingCategory H) ℓ ℓ
  ConjugatorStr .StructureOver.ob[_] = const (GroupHom G H)
  ConjugatorStr .StructureOver.Hom[_][_,_] h φ ψ = isConjugator φ ψ h
  ConjugatorStr .StructureOver.idᴰ {p = φ} = isConjugator1 φ
  ConjugatorStr .StructureOver._⋆ᴰ_ {f = h₁} {g = h₂} {xᴰ = φ} {yᴰ = ψ} {zᴰ = ρ} = isConjugator-· φ ψ ρ h₁ h₂
  ConjugatorStr .StructureOver.isPropHomᴰ {f = h} {xᴰ = φ} {yᴰ = ψ} = isPropIsConjugator {φ} {ψ} h

  Conjugatorsᴰ : Categoryᴰ (DeloopingCategory H) ℓ ℓ
  Conjugatorsᴰ = StructureOver→Catᴰ ConjugatorStr

  Conjugators′ : Category ℓ ℓ
  Conjugators′ = ∫C {C = DeloopingCategory H} Conjugatorsᴰ

  Conjugators : Category ℓ ℓ
  Conjugators = ∫DeloopingCategory H Conjugatorsᴰ
