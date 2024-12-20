module GpdCont.Group.TwoCategory where

open import GpdCont.Prelude
open import GpdCont.Group.MapConjugator
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Isomorphism using (module LocalIso)

import      Cubical.Foundations.Path as Path
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties as GroupHom using (compGroupHom)

module _ (ℓ : Level) where
  {-# INJECTIVE_FOR_INFERENCE isConjugator #-}

  private
    module _ (G : Group ℓ) where
      private open module G = GroupStr (str G) using (_·_)

      group-assoc-brace : ∀ {g h k l} → g · ((h · k) · l) ≡ (g · h) · (k · l)
      group-assoc-brace {g} {h} {k} {l} = sym (cong (g ·_) (G.·Assoc h k l)) ∙ G.·Assoc g h (k · l)

  hcompConjugator : ∀ {G H K : Group ℓ} {φ₁ φ₂ : GroupHom G H} {ψ₁ ψ₂ : GroupHom H K}
    → Conjugator φ₁ φ₂
    → Conjugator ψ₁ ψ₂
    → Conjugator (compGroupHom φ₁ ψ₁) (compGroupHom φ₂ ψ₂)
  hcompConjugator {H} {K} {φ₁ = φ₁*@(φ₁ , φ₁-hom)} {φ₂ = φ₂*@(φ₂ , φ₂-hom)} {ψ₁ = ψ₁*@(ψ₁ , ψ₁-hom)} {ψ₂ = ψ₂*@(ψ₂ , ψ₂-hom)} (h , h-conj) (k , k-conj) = comp-conj where
    open module K = GroupStr (str K) renaming (_·_ to _·ᴷ_)
    open module H = GroupStr (str H) renaming (_·_ to _·ᴴ_)
    _∙ₕ_ = compGroupHom

    h∙ₕk : ⟨ K ⟩
    h∙ₕk = k K.· (ψ₂ h)

    abstract
      isConjugator-k∙ₕk : isConjugator (compGroupHom φ₁* ψ₁*) (compGroupHom φ₂* ψ₂*) h∙ₕk
      isConjugator-k∙ₕk g =
        ψ₁ (φ₁ g) ·ᴷ (k ·ᴷ ψ₂ h) ≡⟨ K.·Assoc _ _ _ ⟩
        (ψ₁ (φ₁ g) ·ᴷ k) ·ᴷ ψ₂ h ≡⟨ cong (K._· ψ₂ h) (k-conj (φ₁ g)) ⟩
        (k ·ᴷ ψ₂ (φ₁ g)) ·ᴷ ψ₂ h ≡⟨ sym $ K.·Assoc _ _ _ ⟩
        k ·ᴷ (ψ₂ (φ₁ g) ·ᴷ ψ₂ h) ≡⟨ cong (k ·ᴷ_) $ sym $ ψ₂-hom .IsGroupHom.pres· (φ₁ g) h ⟩
        k ·ᴷ (ψ₂ (φ₁ g ·ᴴ h))    ≡[ i ]⟨ k ·ᴷ (ψ₂ (h-conj g i)) ⟩
        k ·ᴷ (ψ₂ (h ·ᴴ φ₂ g))    ≡⟨ cong (k ·ᴷ_) (ψ₂-hom .IsGroupHom.pres· h (φ₂ g)) ⟩
        k ·ᴷ (ψ₂ h ·ᴷ ψ₂ (φ₂ g)) ≡⟨ K.·Assoc _ _ _ ⟩
        (k ·ᴷ ψ₂ h) ·ᴷ ψ₂ (φ₂ g) ∎

    comp-conj : Conjugator _ _
    comp-conj .fst = h∙ₕk
    comp-conj .snd = isConjugator-k∙ₕk

  vinvConjugator : ∀ {G H : Group ℓ} {φ ψ : GroupHom G H} (h : Conjugator φ ψ) → Conjugator ψ φ
  vinvConjugator {H} {φ = (φ , _)} {ψ = (ψ , _)} (h , h-conj) = inv-conj where
    open module H = GroupStr (str H)

    inv-conj : Conjugator _ _
    inv-conj .fst = inv h
    inv-conj .snd g =
      ψ g · inv h                 ≡⟨ sym (·IdL _) ∙ cong (_· (ψ g · inv h)) (sym $ ·InvL h) ⟩
      (inv h · h) · (ψ g · inv h) ≡⟨ sym $ group-assoc-brace H ⟩
      (inv h · (h · ψ g) · inv h) ≡[ i ]⟨ inv h · h-conj g (~ i) · (inv h) ⟩
      (inv h · (φ g · h) · inv h) ≡⟨ group-assoc-brace H ⟩
      (inv h · φ g) · (h · inv h) ≡[ i ]⟨ (inv h · φ g) · ·InvR h i ⟩
      (inv h · φ g) · 1g          ≡⟨ ·IdR _ ⟩
      (inv h) · φ g ∎

  twoGroupStr : TwoCategoryStr (Group ℓ) GroupHom Conjugator
  twoGroupStr .TwoCategoryStr.id-hom G = GroupHom.idGroupHom {G = G}
  twoGroupStr .TwoCategoryStr.comp-hom = GroupHom.compGroupHom
  twoGroupStr .TwoCategoryStr.id-rel = idConjugator
  twoGroupStr .TwoCategoryStr.trans = compConjugator
  twoGroupStr .TwoCategoryStr.comp-rel = hcompConjugator

  isTwoCategoryTwoGroupStr : IsTwoCategory (Group ℓ) GroupHom Conjugator twoGroupStr
  isTwoCategoryTwoGroupStr .IsTwoCategory.is-set-rel = isSetConjugator
  isTwoCategoryTwoGroupStr .IsTwoCategory.trans-assoc {y = H} h k l = Conjugator≡ $ sym $ str H .GroupStr.·Assoc _ _ _
  isTwoCategoryTwoGroupStr .IsTwoCategory.trans-unit-left {y = H} h = Conjugator≡ $ str H .GroupStr.·IdL _
  isTwoCategoryTwoGroupStr .IsTwoCategory.trans-unit-right {y = H} h = Conjugator≡ $ str H .GroupStr.·IdR _
  isTwoCategoryTwoGroupStr .IsTwoCategory.comp-rel-id {y = H} {z = K} φ (ψ , ψ-hom) = Conjugator≡ $ sym goal where
    module H = GroupStr (str H)
    module K = GroupStr (str K)
    goal : K.1g K.· ψ H.1g ≡ K.1g
    goal = cong (K.1g K.·_) (ψ-hom .IsGroupHom.pres1) ∙ (K.·IdR K.1g)
  isTwoCategoryTwoGroupStr .IsTwoCategory.comp-rel-trans {y = H} {z = K}
    {g₂ = (ψ₂ , ψ₂-hom)} {g₃ = (ψ₃ , _)}
    (s , _) (t , _) (u , _) (v , v-conj)
    = Conjugator≡ goal where
    module H = GroupStr (str H)
    module K = GroupStr (str K)

    goal : (u K.· v) K.· (ψ₃ (s H.· t)) ≡ (u K.· (ψ₂ s)) K.· (v K.· (ψ₃ t))
    goal =
      (u K.· v) K.· (ψ₃ (s H.· t))      ≡⟨ sym (K.·Assoc _ _ _) ⟩
      u K.· (v K.· (ψ₃ (s H.· t)))      ≡[ i ]⟨ u K.· v-conj (s H.· t) (~ i) ⟩
      u K.· (ψ₂ (s H.· t)) K.· v        ≡[ i ]⟨ u K.· ψ₂-hom .IsGroupHom.pres· s t i K.· v ⟩
      u K.· ((ψ₂ s) K.· ψ₂ t) K.· v     ≡⟨ group-assoc-brace K ⟩
      (u K.· (ψ₂ s)) K.· (ψ₂ t K.· v)   ≡[ i ]⟨ (u K.· (ψ₂ s)) K.· v-conj t i ⟩
      (u K.· (ψ₂ s)) K.· (v K.· (ψ₃ t)) ∎

  isTwoCategoryTwoGroupStr .IsTwoCategory.comp-hom-assoc = GroupHom.compGroupHomAssoc
  isTwoCategoryTwoGroupStr .IsTwoCategory.comp-hom-unit-left _ = GroupHom.GroupHom≡ refl
  isTwoCategoryTwoGroupStr .IsTwoCategory.comp-hom-unit-right = GroupHom.compGroupHomId
  isTwoCategoryTwoGroupStr .IsTwoCategory.comp-rel-assoc
    {z = K} {w = L}
    {g₂ = ψ₂ , _} {k₂ = ρ₂ , ρ₂-hom}
    (s , _) (t , _) (u , _)
    = ConjugatorPathP goal where
    module K = GroupStr (str K)
    module L = GroupStr (str L)

    goal : u L.· (ρ₂ (t K.· ψ₂ s)) ≡ (u L.· ρ₂ t) L.· (ρ₂ (ψ₂ s))
    goal =
      u L.· (ρ₂ (t K.· ψ₂ s))      ≡⟨ cong (u L.·_) (ρ₂-hom .IsGroupHom.pres· _ _) ⟩
      u L.· (ρ₂ t) L.· (ρ₂ (ψ₂ s)) ≡⟨ L.·Assoc u (ρ₂ t) (ρ₂ (ψ₂ s)) ⟩
      (u L.· ρ₂ t) L.· (ρ₂ (ψ₂ s)) ∎

  isTwoCategoryTwoGroupStr .IsTwoCategory.comp-rel-unit-left {x = G} {y = H} {g = ψ , ψ-hom} (s , s-conj) = ConjugatorPathP goal where
    module G = GroupStr (str G)
    module H = GroupStr (str H)

    goal : s H.· ψ G.1g ≡ s
    goal = cong (s H.·_) (ψ-hom .IsGroupHom.pres1) ∙ H.·IdR s
  isTwoCategoryTwoGroupStr .IsTwoCategory.comp-rel-unit-right {y = H} {f = φ , _} (r , r-conj) = ConjugatorPathP goal where
    module H = GroupStr (str H)

    goal : H.1g H.· r ≡ r
    goal = H.·IdL r

  TwoGroup : TwoCategory (ℓ-suc ℓ) ℓ ℓ
  TwoGroup .TwoCategory.ob = Group ℓ
  TwoGroup .TwoCategory.hom = GroupHom
  TwoGroup .TwoCategory.rel = Conjugator
  TwoGroup .TwoCategory.two-category-structure = twoGroupStr
  TwoGroup .TwoCategory.is-two-category = isTwoCategoryTwoGroupStr

  open LocalIso using (isLocallyGroupoidal ; isLocalInverse)

  isLocallyGroupoidalTwoGroup : isLocallyGroupoidal TwoGroup
  isLocallyGroupoidalTwoGroup h .fst = vinvConjugator h
  isLocallyGroupoidalTwoGroup {y = H} (h , _) .snd = is-inv where
    module H = GroupStr (str H)

    open isLocalInverse
    is-inv : isLocalInverse TwoGroup _ _
    is-inv .dom-id = Conjugator≡ (H.·InvR h)
    is-inv .codom-id = Conjugator≡ (H.·InvL h)
