{-# OPTIONS --lossy-unification #-}
open import GpdCont.Prelude hiding (_▷_)

module GpdCont.ActionContainer.Mu (ℓ : Level) (Ix : Type ℓ) where

open import GpdCont.W
open import GpdCont.HomotopySet
open import GpdCont.Univalence
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.Displayed.Base using (module TotalTwoCategory)
open import GpdCont.TwoCategory.StrictFunctor
open import GpdCont.TwoCategory.Family.Base using (Fam)
open import GpdCont.TwoCategory.Product using (Δ)
open import GpdCont.TwoCategory.Algebra
open import GpdCont.TwoCategory.Initial
open import GpdCont.TwoCategory.Isomorphism using (module LocalIso)
open import GpdCont.ActionContainer.Parametrized ℓ
open import GpdCont.ActionContainer.Substitution ℓ Ix
open import GpdCont.GroupAction.Base
open import GpdCont.GroupAction.Equivariant using (isEquivariantMap[_][_,_])
open import GpdCont.GroupAction.Pi using (ΠActionΣ)
open import GpdCont.GroupAction.Sum using (_⊎Action_)
open import GpdCont.GroupAction.TwoCategory using (GroupAction)
open import GpdCont.Group.DirProd using (DirProd ; module DirProd ; mapSndHom)
open import GpdCont.Group.Pi using (mapΠGroup)
open import GpdCont.Group.SymmetricGroup using (𝔖)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (substEquiv)
import      Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum as Sum
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom)
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)
open import Cubical.Algebra.Group.GroupPath using (isGroupoidGroup ; uaGroup)

private
  postulate
    trustme : ∀ {ℓ} {A : Type ℓ} → A

  _×Group_ = DirProd

module _ (F : ActCont[ Ix +1]) where
  private module F = ActCont+1₀ F


  SubstInitial : Type _
  SubstInitial = InitialAlgebra (Subst F)

  μShape : hSet ℓ
  μShape = W[ 1 ∣ s ∈ F.Shape ] ⟨ F.Free/ s ⟩

  -- μShape* : hSet ℓ
  -- μShape* = W[ 1 ∣ s ∈ F.Shape ] ⟨ F.Free s ⟩

  -- TODO: What property of shapes does this encode?
  -- isWellBehaved : ∀ {s : ⟨ F.Shape ⟩} → (⟨ F.Free s ⟩ → ⟨ WSet F.Shape (⟨_⟩ ∘ F.Free) ⟩) → hProp ℓ
  -- isWellBehaved {s} μs .fst = isClassFun (F.action free s) μs
  -- isWellBehaved {s} μs .snd = (isPropIsClassFun (str (WSet _ _)) μs)

  -- μShape : hSet ℓ
  -- μShape = WSubSet F.Shape (⟨_⟩ ∘ F.Free) isWellBehaved

  module _ (ix : Ix) where
    μPos : ⟨ μShape ⟩ → hSet ℓ
    μPos w .fst = WFixᴰΣ {S = ⟨ F.Shape ⟩} {Q = ⟨_⟩ ∘ F.Free/} (⟨_⟩ ∘ F.Param ix) w
    μPos w .snd = isOfHLevelWFixᴰΣ _ 0 (str ∘ F.Param ix) (str ∘ F.Free/) w

    μSymm : ⟨ μShape ⟩ → Group ℓ
    μSymm (sup-W s μs) = (F.Symm (param ix) s) ×Group (ΠGroup {X = ⟨ F.Free/ s ⟩} (μSymm ∘ μs))

    μAction : (w : ⟨ μShape ⟩) → Action (μSymm w) (μPos w)
    μAction = WIndExplicit goal where
      module _
        (sꟳ : ⟨ F.Shape ⟩)
        (sμ : ⟨ F.Free/ sꟳ ⟩ → ⟨ μShape ⟩)
        (μAction : ∀ free → Action (μSymm (sμ free)) (μPos (sμ free)))
        where
        w : ⟨ μShape ⟩
        w = sup-W sꟳ sμ

        goal : Action (μSymm w) (μPos w)
        goal = F.action (param ix) sꟳ ⊎Action ΠActionΣ (F.Free/ sꟳ) (μPos ∘ sμ) μAction

  μ : ActCont.ob Ix
  μ .fst = μShape
  μ .snd w ix .fst = μSymm ix w
  μ .snd w ix .snd .fst = μPos ix w
  μ .snd w ix .snd .snd = μAction ix w

  private
    module μ = ActCont₀ μ
    module F[μ] = ActCont₀ (F [ μ ])

  module _
    (ix : Ix)
    (sꟳ : ⟨ F.Shape ⟩)
    (sμ : ⟨ F.Free/ sꟳ ⟩ → ⟨ μShape ⟩)
    where
    μ-fold-symm : GroupHom (F[μ].Symm ix (sꟳ , sμ)) (μ.Symm ix (sup-W sꟳ sμ))
    μ-fold-symm = idGroupHom

    μ-fold-pos : ⟨ μPos ix (sup-W sꟳ sμ) ⟩ → ⟨ F[μ].Pos ix (sꟳ , sμ) ⟩
    μ-fold-pos = id _

    μ-fold-is-equivariant : isEquivariantMap[ μ-fold-symm , μ-fold-pos ][ F[μ].action ix (sꟳ , sμ) , μ.action ix (sup-W sꟳ sμ) ]
    μ-fold-is-equivariant _ = refl

  μ-fold : ActCont.hom Ix (F [ μ ]) μ
  μ-fold .fst = unfoldWIso .Iso.inv
  μ-fold .snd (sꟳ , sμ) ix .fst = μ-fold-symm ix sꟳ sμ
  μ-fold .snd (sꟳ , sμ) ix .snd .fst = μ-fold-pos ix sꟳ sμ
  μ-fold .snd (sꟳ , sμ) ix .snd .snd = μ-fold-is-equivariant ix sꟳ sμ

  μ-unfold : ActCont.hom Ix μ (F [ μ ])
  μ-unfold .fst = unfoldWIso .Iso.fun
  μ-unfold .snd (sup-W sꟳ sμ) ix .fst = idGroupHom
  μ-unfold .snd (sup-W sꟳ sμ) ix .snd .fst = id _
  μ-unfold .snd (sup-W sꟳ sμ) ix .snd .snd _ = refl

  FAlg : TwoCategory _ _ _
  FAlg = Algebra (Subst F)

  private
    module FAlg = Algebra (Subst F)
    module μ-fold = ActCont₁ μ-fold
    module μ-unfold = ActCont₁ μ-unfold

  μ-alg : FAlg.ob
  μ-alg .fst = μ
  μ-alg .snd = μ-fold

  μ-cata : (alg : FAlg.ob) → FAlg.hom μ-alg alg
  μ-cata (A , φ) = cata-hom where
    module A = ActCont₀ A
    module F[A] = ActCont₀ (F [ A ])
    module φ = ActCont₁ φ

    cata-shape : ⟨ μShape ⟩ → ⟨ A.Shape ⟩
    cata-shape (sup-W sꟳ sμ) = φ.shape-map (sꟳ , sμ ⋆ cata-shape)

    cata-shape-rec : cata-shape ≡ μ-unfold.shape-map ⋆ map-snd (_⋆ cata-shape) ⋆ φ.shape-map
    cata-shape-rec i (sup-W sꟳ sμ) = φ.shape-map (sꟳ , sμ ⋆ cata-shape)

    cata-symm : ∀ ix w → GroupHom (μSymm ix w) (A.Symm ix (cata-shape w))
    cata-symm ix w@(sup-W sꟳ sμ) = {! !} where
      foo : GroupHom (F[A].Symm ix (sꟳ , sμ ⋆ cata-shape)) (A.Symm ix (cata-shape w))
      foo = φ.symm-map ix (sꟳ , sμ ⋆ cata-shape)

    cata-pos : ∀ ix w → ⟨ A.Pos ix (cata-shape w) ⟩ → ⟨ μPos ix w ⟩
    cata-pos ix w@(sup-W sꟳ sμ) = foo ⋆ bar  where
      foo : ⟨ A.Pos ix (cata-shape w) ⟩ → ⟨ F[A].Pos ix (sꟳ , sμ ⋆ cata-shape) ⟩
      foo = φ.pos-map ix (sꟳ , sμ ⋆ cata-shape)

      bar : ⟨ F[A].Pos ix (sꟳ , sμ ⋆ cata-shape) ⟩ → ⟨ μPos ix w ⟩
      bar (inl p) = inl p
      bar (inr (p , pos-A)) = inr (p , cata-pos ix (sμ p) pos-A)

    cata : ActCont.hom Ix μ A
    cata .fst = cata-shape
    cata .snd w ix .fst = cata-symm ix w
    cata .snd w ix .snd .fst = cata-pos ix w
    cata .snd w ix .snd .snd = {! !}

    cata-is-algebra-hom : ActCont.comp-hom Ix μ-fold cata ≡ ActCont.comp-hom Ix (subst-hom F cata) φ
    cata-is-algebra-hom = {! !}

    cata-hom : FAlg.hom _ _
    cata-hom .fst = cata
    cata-hom .snd = LocalIso.pathToLocalIso (ActCont Ix) cata-is-algebra-hom

{-
  μ-alg-hom : (alg : FAlg.ob) → FAlg.hom μ-alg alg
  μ-alg-hom (A , alg) = def where
    module A = ActCont₀ A
    module FA = ActCont₀ (F [ A ])
    module alg = ActCont₁ alg

    ana-shape : ⟨ μShape ⟩ → ⟨ A.Shape ⟩
    ana-shape (sup-W sꟳ μ-shapes) = alg.shape-map (sꟳ , μ-shapes ⋆ ana-shape)

    ana-symm : (w : ⟨ μShape ⟩) (ix : Ix) → GroupHom (μSymm w ix) (A.Symm ix (ana-shape w))
    ana-symm (sup-W sꟳ μ-shapes) ix = {! !}

    ana-pos : (w : ⟨ μShape ⟩) (ix : Ix) → ⟨ A.Pos ix (ana-shape w) ⟩ → ⟨ μPos w ix ⟩
    ana-pos w@(sup-W sꟳ μ-shapes) ix = one ⋆ two where
      one : ⟨ A.Pos ix (ana-shape w) ⟩ → ⟨ FA.Pos ix (sꟳ , μ-shapes ⋆ ana-shape) ⟩
      one = alg.pos-map ix (sꟳ , μ-shapes ⋆ ana-shape)

      two : ⟨ FA.Pos ix (sꟳ , μ-shapes ⋆ ana-shape) ⟩ → ⟨ μPos w ix ⟩
      two (inl x) = here {! !}
      two (inr x) = {! !}

    ana : ActCont.hom Ix μ A
    ana .fst = ana-shape
    ana .snd w ix .fst = ana-symm w ix
    ana .snd w ix .snd .fst = ana-pos w ix
    ana .snd w ix .snd .snd = {! !}

    def : FAlg.hom (μ , μ-fold) (A , alg)
    def .fst = ana
    def .snd = {! !}
  -- μ-alg-hom (A , alg) .fst .fst = WIndExplicit λ s _ sub → alg .fst (s , sub)
  -- μ-alg-hom (A , alg) .fst .snd = WIndExplicit λ s xx f ix → {! f  !}
  -- μ-alg-hom (A , alg) .snd = {! !}

{-
  isProp-μ-initial-hom : (alg : FAlg.ob) → isProp (FAlg.hom μ-alg alg)
  isProp-μ-initial-hom alg f*@(f , is-hom-f) g*@(g , is-hom-g) = FAlg.₁≡ {x = μ-alg} {y = alg} {f = f*} {g = g*} lemma₁ {! !} where
    lemma₁ : f ≡ g
    lemma₁ = {! is-hom-f .fst!}

  -- μ-initial-eq : (alg : FAlg.ob) (f g : FAlg.hom μ-alg alg) → f ≡ g
  -- μ-initial-eq alg f g = ΣPathP (ΣPathP (funExt {! f .snd !} , {! !}) , {! !})

  μ-initial' : (alg : FAlg.ob) (f g : FAlg.hom μ-alg alg) → isContr (f ≡ g)
  μ-initial' alg = isProp→isContrPath $ isProp-μ-initial-hom alg
  -- μ-initial' alg f g .fst = μ-initial-eq alg f g
  -- μ-initial' alg f g .snd = {! !}

  μ-initial : SubstInitial F
  μ-initial .fst = μ-alg
  μ-initial .snd alg f g = {! isContrRetract {! !} {! !} {! !} (μ-initial' alg f g) !}
  -}
  -}
