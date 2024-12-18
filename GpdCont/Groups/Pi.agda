open import GpdCont.Prelude

module GpdCont.Groups.Pi (ℓ : Level) where

open import GpdCont.HomotopySet
open import GpdCont.Equiv using (isSet→section-equivToIso)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Groups
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)

private
  module Group = Category (GroupCategory {ℓ})

module _ (K : hSet ℓ) (G : ⟨ K ⟩ → Group.ob) where
  open import GpdCont.Categories.Products (GroupCategory {ℓ}) ℓ

  private
    Group→hSet : (H : Group.ob) → hSet ℓ
    Group→hSet H .fst = ⟨ H ⟩
    Group→hSet H .snd = str H .GroupStr.is-set

    Π : Group.ob
    Π = ΠGroup G

    proj : ∀ k → Group.Hom[ Π , G k ]
    proj k .fst φ = φ k
    proj k .snd .IsGroupHom.pres· φ ψ = refl
    proj k .snd .IsGroupHom.pres1 = refl
    proj k .snd .IsGroupHom.presinv φ = refl

  univ-iso : (H : Group.ob) → Iso Group.Hom[ H , Π ] (∀ k → Group.Hom[ H , G k ])
  univ-iso H =
    Group.Hom[ H , Π ] Iso⟨⟩
    Σ[ φ ∈ (⟨ H ⟩ → (k : ⟨ K ⟩) → ⟨ G k ⟩) ] IsGroupHom (str H) φ (str Π) Iso⟨ Σ-cong-iso-fst flipIso ⟩
    Σ[ φ ∈ ((k : ⟨ K ⟩) → ⟨ H ⟩ → ⟨ G k ⟩) ] IsGroupHom (str H) (flip φ) (str Π) Iso⟨ Σ-cong-iso-snd is-group-hom-iso ⟩
    Σ[ φ ∈ ((k : ⟨ K ⟩) → ⟨ H ⟩ → ⟨ G k ⟩) ] (∀ k → IsGroupHom (str H) (φ k) (str (G k))) Iso⟨ invIso Σ-Π-Iso ⟩
    (∀ k → Group.Hom[ H , G k ]) Iso∎
    where
      is-group-hom-iso : (φ : (k : ⟨ K ⟩) → ⟨ H ⟩ → ⟨ G k ⟩)
        → Iso
          (IsGroupHom (str H) (flip φ) (str Π))
          (∀ k → IsGroupHom (str H) (φ k) (str (G k)))
      is-group-hom-iso φ = isProp→Iso
        (isPropIsGroupHom _ _)
        (isPropΠ λ k → isPropIsGroupHom _ _)
        (λ where
          φ*-hom k .IsGroupHom.pres· g h → φ*-hom .IsGroupHom.pres· g h ≡$ k
          φ*-hom k .IsGroupHom.presinv g → φ*-hom .IsGroupHom.presinv g ≡$ k
          φ*-hom k .IsGroupHom.pres1 → φ*-hom .IsGroupHom.pres1 ≡$ k
        )
        (λ where
          φ-hom .IsGroupHom.pres· g h → funExt (λ k → φ-hom k .IsGroupHom.pres· g h)
          φ-hom .IsGroupHom.presinv g → funExt (λ k → φ-hom k .IsGroupHom.presinv g)
          φ-hom .IsGroupHom.pres1 → funExt (λ k → φ-hom k .IsGroupHom.pres1)
        )

  private module _ (H : Group.ob) where
    univ-fun : Group.Hom[ H , Π ] → (∀ k → Group.Hom[ H , G k ])
    univ-fun φ = λ k → φ Group.⋆ (proj k)

    univ-equiv' : Group.Hom[ H , Π ] ≃ (∀ k → Group.Hom[ H , G k ])
    univ-equiv' = isoToEquiv (univ-iso H)

    univ-fun≡ : equivFun univ-equiv' ≡ univ-fun
    univ-fun≡ = funExt λ φ → funExt λ k → GroupHom≡ refl

    is-univ : isEquiv univ-fun
    is-univ = subst {x = equivFun univ-equiv'} {y = univ-fun} isEquiv univ-fun≡ (equivIsEquiv univ-equiv')

    univ-equiv : Group.Hom[ H , Π ] ≃ (∀ k → Group.Hom[ H , G k ])
    univ-equiv .fst = _
    univ-equiv .snd = is-univ

    univ-equiv≡ : univ-equiv' ≡ univ-equiv
    univ-equiv≡ = equivEq univ-fun≡

  GroupProduct : Product K G
  GroupProduct .UniversalElement.vertex = ΠGroup G
  GroupProduct .UniversalElement.element = proj
  GroupProduct .UniversalElement.universal = is-univ

  module _ (H : Group.ob) where
    opaque
      univ-coherence : NotationAt.univ-iso K G GroupProduct H ≡ univ-iso H
      univ-coherence =
        equivToIso (univ-equiv H) ≡⟨ cong equivToIso (sym (univ-equiv≡ H)) ⟩
        equivToIso (isoToEquiv (univ-iso H)) ≡⟨ isSet→section-equivToIso Group.isSetHom (isSetΠ (λ k → Group.isSetHom)) (univ-iso H) ⟩
        univ-iso H ∎

    univ-inv-coherence : Iso.inv (NotationAt.univ-iso K G GroupProduct H) ≡ univ-iso H .Iso.inv
    univ-inv-coherence = cong Iso.inv univ-coherence

GroupProducts = GroupProduct
