{-# OPTIONS --lossy-unification #-}
open import GpdCont.Prelude hiding (_▷_)

module GpdCont.ActionContainer.AsSymmetricContainer (ℓ : Level) where

open import GpdCont.HLevels
open import GpdCont.Univalence
open import GpdCont.Equiv using (equivΠDomain)
open import GpdCont.TwoCategory.Base
open import GpdCont.TwoCategory.StrictFunctor using (StrictFunctor ; compStrictFunctor)
open import GpdCont.TwoCategory.StrictFunctor.LocalFunctor using (LocalFunctor ; isLocallyFullyFaithful)
open import GpdCont.TwoCategory.CompositeFunctor using (isLocallyFullyFaithfulCompositeRestrict)
open import GpdCont.TwoCategory.Displayed.StrictFunctor using (StrictFunctorᴰ)
import      GpdCont.Delooping as Delooping
import      GpdCont.Delooping.Product as 𝔹Prod
open import GpdCont.Group.DirProd using (module DirProd ; mapSndHom) renaming (DirProd to _⊗_)
open import GpdCont.Group.Pi using (mapΠGroup)
open import GpdCont.GroupAction.Base using (Action ; module ActionProperties)
open import GpdCont.GroupAction.Pi using (ΠAction ; ΠActionΣ)
open import GpdCont.GroupAction.AssociatedBundle using (∫) renaming (associatedBundle to 𝔹ᴰ)
open import GpdCont.GroupAction.Delooping using (isConnectedDeloopingBase)
open import GpdCont.ActionContainer.AsFamily ℓ
  using (Fam𝔹 ; isLocallyFullyFaithfulFam𝔹)
  renaming (FamAction to ActCont)

open import GpdCont.SetBundle.Base ℓ using (module SetBundleNotation) renaming (SetBundle to SymmCont)
open import GpdCont.SetBundle.Summation ℓ using (SetBundleΣ ; isLocallyFullyFaithfulΣ-at-connBase)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Pi using (ΠGroup)

ActToSymmCont : StrictFunctor ActCont SymmCont
ActToSymmCont = compStrictFunctor Fam𝔹 SetBundleΣ

isLocallyFullyFaithfulActToSymmCont : isLocallyFullyFaithful ActToSymmCont
isLocallyFullyFaithfulActToSymmCont =
  isLocallyFullyFaithfulCompositeRestrict Fam𝔹 SetBundleΣ isLocallyFullyFaithfulFam𝔹 Σ-ff-restrict
  where
    open import Cubical.Categories.Functor using (Functor)
    module Fam𝔹 = StrictFunctor Fam𝔹

    Σ-ff-restrict : ∀ F G → Functor.isFullyFaithful (LocalFunctor SetBundleΣ (Fam𝔹.₀ F) (Fam𝔹.₀ G))
    Σ-ff-restrict F G = isLocallyFullyFaithfulΣ-at-connBase (Fam𝔹.₀ F) (Fam𝔹.₀ G) λ j → isConnectedDeloopingBase ℓ (F .snd j)

private
  module SymmCont = TwoCategory SymmCont
  module 𝔹 = StrictFunctor ActToSymmCont

private
  module ActCont = TwoCategory ActCont
  module ActCont₀ (F : ActCont.ob) where

    Shape : hSet _
    Shape = F .fst

    Pos : ⟨ Shape ⟩ → hSet _
    Pos s = F .snd s .snd .fst

    Symm : ⟨ Shape ⟩ → Group _
    Symm s = F .snd s .fst

    action : ∀ s → Action (Symm s) (Pos s)
    action s = F .snd s .snd .snd

    module _ {s : ⟨ Shape ⟩} where
      private
        module Symm = GroupStr (str (Symm s))
      open Symm using (_·_ ; inv) public

      action≃ : ⟨ Symm s ⟩ → ⟨ Pos s ⟩ ≃ ⟨ Pos s ⟩
      action≃ = action s .Action.action

      _▷_ : ⟨ Symm s ⟩ → ⟨ Pos s ⟩ → ⟨ Pos s ⟩
      _▷_ g = equivFun (action≃ g)

      ·-▷-assoc : (g h : ⟨ Symm s ⟩) (p : ⟨ Pos s ⟩) → (g · h) ▷ p ≡ h ▷ (g ▷ p)
      ·-▷-assoc g h p = ActionProperties.action-comp (action s) g h ≡$ p

module SymmCont₀ (F : SymmCont.ob) where
  open SetBundleNotation using (Base ; Fiber)

  Shape = Base F
  Pos = Fiber F

SubstAct' : (F G : ActCont.ob) → ActCont.ob
SubstAct' F G = Shape , Bundled where
  module F = ActCont₀ F
  module G = ActCont₀ G

  open Delooping using (𝔹)

  Shape : hSet _
  Shape = Σʰ[ 2 ∣ s ∈ F.Shape ] Πʰ[ 2 ∣ x ∈ 𝔹 (F.Symm s) ] (⟨ 𝔹ᴰ (F.action s) x ⟩ →₂ G.Shape)

  module _ ((s , t) : ⟨ Shape ⟩) where
    -- ∫t : ∀ {s} → ∫ {G = F.Symm s} (F.action s) → ⟨ G.Shape ⟩
    -- ∫t (x , p) = t x p

    module _ (x : 𝔹 (F.Symm s)) where
      Symmᴰ :  Group _
      Symmᴰ = ΠGroup {X = ⟨ 𝔹ᴰ (F.action s) x ⟩} λ p → G.Symm (t x p)

      Posᴰ : hSet _
      Posᴰ =
        Σʰ[ 2 ∣ p ∈ 𝔹ᴰ (F.action s) x ]
        G.Pos (t x p)

      actionᴰ : Action Symmᴰ Posᴰ
      actionᴰ = ΠActionΣ (𝔹ᴰ (F.action s) x) (G.Pos ∘ t x) (G.action ∘ t x)

    Symm : Group _
    Symm = ΠGroup {X = 𝔹 (F.Symm s)} λ x → ΠGroup {X = ⟨ 𝔹ᴰ (F.action s) x ⟩} λ p → G.Symm (t x p)

    Pos : hSet _
    Pos = Πʰ[ 2 ∣ x ∈ 𝔹 (F.Symm s) ] (Posᴰ x)

    action : Action Symm Pos
    action = ΠAction Posᴰ actionᴰ

    Bundled : Σ[ G ∈ _ ] Σ[ P ∈ hSet _ ] Action G P
    Bundled .fst = Symm
    Bundled .snd .fst = Pos
    Bundled .snd .snd = action

SubstAct : (F G : ActCont.ob) → ActCont.ob
SubstAct F G = Shape , Bundled where
  module F = ActCont₀ F
  module G = ActCont₀ G

  Shape : hSet _
  Shape = Σʰ[ 2 ∣ s ∈ F.Shape ] (⟨ F.Pos s ⟩ →₂ G.Shape)

  module _ ((s , t) : ⟨ Shape ⟩) where
    Symm : Group _
    Symm = F.Symm s ⊗ ΠGroup (G.Symm ∘ t)

    Pos : hSet _
    Pos =
      Σʰ[ 2 ∣ p ∈ F.Pos s ]
      Πʰ[ 2 ∣ g ∈ ⟨ F.Symm s ⟩ ]
      G.Pos (t (g F.▷ p))

    action : Action Symm Pos
    action .Action.action (f , g) .fst (p , q) = (f F.▷ p) , λ f′ → g (f′ F.▷ (f F.▷ p)) G.▷ subst (λ p → ⟨ G.Pos (t p) ⟩) (F.·-▷-assoc f f′ p) (q (f F.· f′))
    action .Action.action (f , g) .snd = {! !}
    action .Action.pres· = {! !}

    Bundled : Σ[ G ∈ _ ] Σ[ P ∈ hSet _ ] Action G P
    Bundled .fst = Symm
    Bundled .snd .fst = Pos
    Bundled .snd .snd = action

SubstSymm : (F G : SymmCont.ob) → SymmCont.ob
SubstSymm F G = Shape , Pos where
  module F = SymmCont₀ F
  module G = SymmCont₀ G

  Shape : hGroupoid _
  Shape = Σʰ[ 3 ∣ s ∈ F.Shape ] (⟨ F.Pos s ⟩ →₃ G.Shape)

  Pos : ⟨ Shape ⟩ → hSet _
  Pos (s , f) = Σʰ[ 2 ∣ p ∈ F.Pos s ] G.Pos (f p)

test : (F G : ActCont.ob) → ⟨ SymmCont₀.Shape (𝔹.₀ (SubstAct F G)) ⟩ ≃ {! !}
test F G =
  Σ[ (s , f) ∈ ⟨ F[G].Shape ⟩ ] 𝔹 (F[G].Symm (s , f)) ≃⟨ Σ-assoc-≃ ⟩
  Σ[ s ∈ ⟨ F.Shape ⟩ ] Σ[ f ∈ (⟨ F.Pos s ⟩ → ⟨ G.Shape ⟩) ] 𝔹 (F[G].Symm (s , f)) ≃⟨ Σ-cong-equiv-snd (λ s → {! !}) ⟩
  Σ[ s ∈ ⟨ F.Shape ⟩ ] Σ[ f ∈ (⟨ F.Pos s ⟩ → ⟨ G.Shape ⟩) ] (𝔹 (F.Symm s)) × (∀ p → 𝔹 (G.Symm (f p)))
    ≃⟨ Σ-cong-equiv-snd (λ s → strictEquiv (λ (f , x , y) → x , f , y) (λ (x , f , y) → f , x , y)) ⟩
  Σ[ s ∈ ⟨ F.Shape ⟩ ] (𝔹 (F.Symm s)) × (Σ[ f ∈ (⟨ F.Pos s ⟩ → ⟨ G.Shape ⟩) ] ∀ p → 𝔹 (G.Symm (f p)))
    ≃⟨ Σ-cong-equiv-snd (λ { s → ≃-× (idEquiv _) $ invEquiv Σ-Π-≃ }) ⟩
  Σ[ s ∈ ⟨ F.Shape ⟩ ] (𝔹 (F.Symm s)) × (⟨ F.Pos s ⟩ → Σ[ t ∈ ⟨ G.Shape ⟩ ] 𝔹 (G.Symm t))
    ≃⟨ invEquiv Σ-assoc-≃ ⟩
  Σ[ s* ∈ ⟨ 𝔹F.Shape ⟩ ] (⟨ F.Pos (s* .fst) ⟩ → ⟨ 𝔹G.Shape ⟩) ≃∎
  where
    module F = ActCont₀ F
    module G = ActCont₀ G
    module F[G] = ActCont₀ (SubstAct F G)

    module 𝔹F = SymmCont₀ (𝔹.₀ F)
    module 𝔹G = SymmCont₀ (𝔹.₀ G)
    module 𝔹F[𝔹G] = SymmCont₀ (SubstSymm (𝔹.₀ F) (𝔹.₀ G))

    open Delooping using (𝔹)

shuffle : ∀ {ℓ} {A : Type ℓ}
  → {B : A → Type ℓ}
  → {C : (a : A) → B a → Type ℓ}
  → {D : Type ℓ}
  → Iso
    (Σ[ a ∈ A ] ((Σ[ b ∈ B a ] C a b) → D))
    (Σ[ (a , b) ∈ Σ A B ] (C a b → D))
shuffle .Iso.fun (a , f) = (a , {! !}) , {! !}
shuffle .Iso.inv ((a , b) , f) = a , λ { (b' , c) → f {!c!} }
shuffle .Iso.rightInv = {! !}
shuffle .Iso.leftInv = {! !}

test' : (F G : ActCont.ob) → ⟨ SymmCont₀.Shape (𝔹.₀ (SubstAct' F G)) ⟩ ≃ ⟨ SymmCont₀.Shape (SubstSymm (𝔹.₀ F) (𝔹.₀ G)) ⟩
test' F G =
  Σ[ s* ∈ ⟨ F[G].Shape ⟩ ] 𝔹 (F[G].Symm s*) ≃⟨ Σ-assoc-≃ ⟩
  Σ[ s ∈ ⟨ F.Shape ⟩ ] Σ[ f ∈ (∀ x → ⟨ 𝔹ᴰ (F.action s) x ⟩ → ⟨ G.Shape ⟩) ] 𝔹 (F[G].Symm (s , f)) ≃⟨ {! !} ⟩
  Σ[ s ∈ ⟨ F.Shape ⟩ ] Σ[ f ∈ (∀ x → ⟨ 𝔹ᴰ (F.action s) x ⟩ → ⟨ G.Shape ⟩) ] (∀ x p → 𝔹 (G.Symm (f x p))) ≃⟨ Σ-cong-equiv-snd (λ s → invEquiv Σ-Π-≃) ⟩
  Σ[ s ∈ ⟨ F.Shape ⟩ ] (∀ x → Σ[ f ∈ (⟨ 𝔹ᴰ (F.action s) x ⟩ → ⟨ G.Shape ⟩) ] (∀ p → 𝔹 (G.Symm (f p)))) ≃⟨ Σ-cong-equiv-snd (λ s → equivΠCod λ x → invEquiv Σ-Π-≃) ⟩
  Σ[ s ∈ ⟨ F.Shape ⟩ ] ((x : 𝔹 (F.Symm s)) → (p : ⟨ 𝔹ᴰ (F.action s) x ⟩) → Σ[ t ∈ ⟨ G.Shape ⟩ ] (𝔹 (G.Symm t))) ≃⟨ Σ-cong-equiv-snd (λ s → invEquiv curryEquiv) ⟩
  Σ[ s ∈ ⟨ F.Shape ⟩ ] ((Σ[ x ∈ 𝔹 (F.Symm s) ] ⟨ 𝔹ᴰ (F.action s) x ⟩) → (Σ[ t ∈ ⟨ G.Shape ⟩ ] (𝔹 (G.Symm t)))) ≃⟨ {! !} ⟩
  -- Σ[ s ∈ ⟨ F.Shape ⟩ ] (∫ (F.action s) → (Σ[ t ∈ ⟨ G.Shape ⟩ ] (𝔹 (G.Symm t)))) ≃⟨ {! !} ⟩
  Σ[ s ∈ ⟨ F.Shape ⟩ ] Σ[ x ∈ 𝔹 (F.Symm s) ] (⟨ 𝔹ᴰ (F.action s) x ⟩ → ⟨ 𝔹G.Shape ⟩) ≃⟨ invEquiv Σ-assoc-≃ ⟩
  Σ[ (s , x) ∈ ⟨ 𝔹F.Shape ⟩ ] (⟨ 𝔹ᴰ (F.action s) x ⟩ → ⟨ 𝔹G.Shape ⟩) ≃∎
  where
    module F = ActCont₀ F
    module G = ActCont₀ G
    module F[G] = ActCont₀ (SubstAct' F G)

    module 𝔹F = SymmCont₀ (𝔹.₀ F)
    module 𝔹G = SymmCont₀ (𝔹.₀ G)
    module 𝔹F[𝔹G] = SymmCont₀ (SubstSymm (𝔹.₀ F) (𝔹.₀ G))

    open Delooping using (𝔹)

    foo : Iso
      (Σ[ s ∈ ⟨ F.Shape ⟩ ] (∫ (F.action s) → (Σ[ t ∈ ⟨ G.Shape ⟩ ] (𝔹 (G.Symm t)))))
      (Σ[ (s , x) ∈ ⟨ 𝔹F.Shape ⟩ ] (⟨ 𝔹ᴰ (F.action s) x ⟩ → ⟨ 𝔹G.Shape ⟩))
    foo .Iso.fun (s , f) .fst .fst = s
    foo .Iso.fun (s , f) .fst .snd = {!f ? !}
    foo .Iso.fun (s , f) .snd = {! !}
    foo .Iso.inv = {! !}
    foo .Iso.rightInv = {! !}
    foo .Iso.leftInv = {! !}

module Multiplication (F G : ActCont.ob) where
  private
    module F = ActCont₀ F
    module G = ActCont₀ G
    module F[G] = ActCont₀ (SubstAct F G)

    -- module 𝔹F = SymmCont₀ (𝔹.₀ F)
    -- module 𝔹G = SymmCont₀ (𝔹.₀ G)
    -- module 𝔹F[𝔹G] = SymmCont₀ (SubstSymm (𝔹.₀ F) (𝔹.₀ G))

    open Delooping using (𝔹)

  inv-shape : ⟨ SymmCont₀.Shape (SubstSymm (𝔹.₀ F) (𝔹.₀ G)) ⟩ → ⟨ SymmCont₀.Shape (𝔹.₀ (SubstAct F G)) ⟩
  -- inv-shape ((s , x) , y) = (s , λ p → {!y!}) , {! !}
  inv-shape = uncurry $ uncurry λ s → Delooping.elim (F.Symm s) {! !}
    (λ { y → (s , y ⋆ fst) , 𝔹.⋆ })
    -- (λ { g i y → (s , {!y!}) , {! !} })
    (λ { g → funExtNonDep λ { eq → ΣPathP (ΣPathP (refl′ s , funExt λ pos → {!ua→⁻ eq !}) , {! !}) } })
    {! !}

  mul-shape : ⟨ SymmCont₀.Shape (𝔹.₀ (SubstAct F G)) ⟩ → ⟨ SymmCont₀.Shape (SubstSymm (𝔹.₀ F) (𝔹.₀ G)) ⟩
  mul-shape ((s , f) , x) = (s , 𝔹.⋆) , λ { p → f p , π x p }
    where
      π : 𝔹 (F.Symm s ⊗ ΠGroup (G.Symm ∘ f)) → ∀ p → 𝔹 (G.Symm (f p))
      π = 𝔹Prod.DeloopingSnd (F.Symm s) (ΠGroup $ G.Symm ∘ f) ⋆ 𝔹Prod.𝔹Π→Π𝔹 (G.Symm ∘ f)

  mul-pos : ∀ s* → ⟨ SymmCont₀.Pos (SubstSymm (𝔹.₀ F) (𝔹.₀ G)) (mul-shape s*) ⟩ → ⟨ SymmCont₀.Pos (𝔹.₀ (SubstAct F G)) s* ⟩
  mul-pos = uncurry λ where
    (s , f) → Delooping.elimSet (F[G].Symm (s , f)) (λ x → isSet→ (str (SymmCont₀.Pos (𝔹.₀ (SubstAct F G)) ((s , f) , x))))
      (λ { (p , q) → p , λ { g → the ⟨ G.Pos (f (g F.▷ p)) ⟩ {!the ⟨ G.Pos _ ⟩ q !} } })
      {! !}

  mul : SymmCont.hom (𝔹.₀ (SubstAct F G)) (SubstSymm (𝔹.₀ F) (𝔹.₀ G))
  mul .fst = mul-shape
  mul .snd = mul-pos
