{-# OPTIONS --lossy-unification #-}
module GpdCont.QuotientContainer.LiftFunctor where

open import GpdCont.Prelude

open import GpdCont.QuotientContainer.Base
open import GpdCont.QuotientContainer.Category

open import GpdCont.QuotientContainer.Premorphism as PreMor using (Premorphism)
import GpdCont.QuotientContainer.Morphism as QMor
import GpdCont.QuotientContainer.Lift as Lift

open import GpdCont.Coffin.GroupoidContainerInclusion using (Coffin→GroupoidContainer)
open import GpdCont.SymmetricContainer.Base
open import GpdCont.Delooping.Map renaming (map to 𝔹-map ; map-id to 𝔹-map-id)

open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (isSetGroupHom ; makeIsGroupHom ; idGroupHom ; GroupHom≡)

private
  variable
    ℓ : Level

  ↑ : (Q : QCont ℓ) → SymmetricContainer ℓ
  ↑ Q = Coffin→GroupoidContainer (Lift.↑ Q)

open Category hiding (id)

open QMor using (idQCont)

{-
private
  module ↑-map (Q R : QCont ℓ) where
    module Q = QCont Q
    module R = QCont R
    module ↑Q = SymmetricContainer (↑ Q)
    module ↑R = SymmetricContainer (↑ R)

    module _ (s) (u : Q.Shape → R.Shape) (f : Premorphism Q R u) where
      module f = Premorphism f
    
      φ* : GroupHom (Q.SymmGroup s) (R.SymmGroup (u s))
      φ* = f.symmHom s

      φ-pos : R.Pos (u s) → Q.Pos s
      φ-pos = f.pos-mor _

    φ-pos-wd : ∀ {s} (u : Q.Shape → R.Shape) → (f f′ : Premorphism Q R u) (r : PreMor.PremorphismEquiv f f′) → φ-pos s u f ≡ φ-pos s u f′
    φ-pos-wd u f f′ r = {!PreMor.isWellDefinedSymmHom !}

    φ : ∀ s → (α : QMor.Morphism Q R) → GroupHom (Q.SymmGroup s) (R.SymmGroup (α .QMor.Morphism.shape-mor s))
    φ s = QMor.MorphismElim {Q = Q} {S = R} (λ _ → isSetGroupHom {G = Q.SymmGroup s} {H = R.SymmGroup _}) (φ* s) (PreMor.isWellDefinedSymmHom {Q = Q} {R = R} {s = s})

    φ-compute : ∀ s (u : Q.Shape → R.Shape) (f : Premorphism Q R u) → φ s (QMor.pre→mor f) ≡ φ* s u f
    φ-compute s = QMor.MorphismElimCompute {Q = Q} {S = R} (λ α → isSetGroupHom {G = Q.SymmGroup s} {H = R.SymmGroup (α .QMor.Morphism.shape-mor s)}) (φ* s) PreMor.isWellDefinedSymmHom

    module _ (α : QMor.Morphism Q R) where
      open module α = QMor.Morphism α renaming (shape-mor to u)

      𝔹φ : ∀ {s : Q.Shape} (σ : Lift.↑Symm Q s) → Lift.↑Symm R (u s)
      𝔹φ {s} = 𝔹-map (φ s α)

      ↑-shape-mor : ↑Q.Shape →  ↑R.Shape
      ↑-shape-mor = Lift.↑Shape-uncurry Q λ s σ → u s , 𝔹φ σ

      ↑-pos-path : ∀ (s : ↑Q.Shape) → ↑R.Pos (↑-shape-mor s) → ↑Q.Pos s
      ↑-pos-path = Lift.↑Shape-uncurry Q λ s → Lift.↑SymmElim.elimSet Q s {B = Motive} (λ σ → is-set-↑RPos→↑QPos (s , σ)) (elim* α) elim*-loop where
        is-set-↑RPos→↑QPos : ∀ s → isSet (↑R.Pos (↑-shape-mor s) → ↑Q.Pos s)
        is-set-↑RPos→↑QPos s = isSet→ (↑Q.is-set-pos s)

        Motive : ∀ {s} → Lift.↑Symm Q s → Type _
        Motive σ = ↑R.Pos (↑-shape-mor (_ , σ)) → ↑Q.Pos (_ , σ)

        elim* : (α : QMor.Morphism Q R) → ∀ {s} → R.Pos (α .QMor.Morphism.shape-mor s) → Q.Pos s
        elim* α {s} = QMor.MorphismElim {P = λ (α : QMor.Morphism Q R) → ∀ {s} → R.Pos (α .QMor.Morphism.shape-mor s) → Q.Pos s}
          (λ α → isSetImplicitΠ λ q → isSet→ (Q.is-set-pos q))
          (λ u f {s} → φ-pos s u f)
          (λ { f f′ r i {s} → φ-pos-wd _ f f′ r i }) α

        elim*-loop : ∀ {s} (σ : Q.Symm s) → PathP (λ i → Motive (Lift.↑SymmElim.loop σ i)) (elim* α) (elim* α)
        elim*-loop {s} σ = {! !}

  module _ (Q : QCont ℓ) where
    open ↑-map Q Q
  
    opaque
      φ-id : ∀ s → φ s (idQCont {Q = Q}) ≡ idGroupHom {G = Q.SymmGroup s}
      φ-id s =
        φ s (idQCont {Q = Q}) ≡⟨ φ-compute _ _ _ ⟩
        φ* s (id _) (PreMor.idPremorphism Q) ≡⟨ GroupHom≡ refl ⟩
        idGroupHom ∎


↑-map : {Q R : QCONT ℓ .ob} → (α : QCONT ℓ [ Q , R ]) → GContMorphism (↑ Q) (↑ R)
↑-map {Q} {R} α .GContMorphism.shape-map = ↑-map.↑-shape-mor Q R α
↑-map {Q} {R} α .GContMorphism.pos-map = ↑-map.↑-pos-path Q R α

↑-map-id : (Q : QCont ℓ) → ↑-map (QMor.idQCont {Q = Q}) ≡ GContId (↑ Q)
↑-map-id Q = GContMorphism≡ (funExt (Lift.↑Shape-uncurry Q λ s σ i → s , goal s i σ)) {! !} where
  open ↑-map Q Q

  goal : ∀ s → 𝔹φ QMor.idQCont ≡ id (Lift.↑Symm Q s)
  goal s =
    𝔹-map (φ s QMor.idQCont) ≡⟨ cong 𝔹-map (φ-id Q s) ⟩
    𝔹-map idGroupHom ≡⟨ 𝔹-map-id (Q.SymmGroup _) ⟩
    id _ ∎
-}
